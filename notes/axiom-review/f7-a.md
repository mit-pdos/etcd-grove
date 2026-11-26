# F7 review, group A (auth-on client calls), `etcd-safe-f7` @ `d946f6cbda`

File: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthViewDist.lean` (AVD). Go: `.lake/go-src/etcd`
(`client/v3/{client,retry,retry_interceptor}.go`, server apply/auth). Read-only, no Lean built.

## Main finding: the member names `A` are free, so `A mid`'s facts can be refuted by the caller

`New_user_dist`, `KV_GetOn_dist` and `Txn_CommitOn_dist` quantify `A : w64 → auth.AuthNames` universally. They
constrain it only by `∀ a b, A a = A b → a = b`. Nothing ties `A` to `Γ`, to `membersAt`/`etcdAddrAt` (`etcdSvc Γ mid`),
or to any invariant that holds the authority of `(A mid).hist`. The success arms then assert facts at `A mid`:
`passwordChecked`/`enabledVerdict (.on (A mid))` (both give `authStateAt (A mid) i st`, that is
`monoListIdxOwn (A mid).hist i st`), and `authFloorD`/`rangeClassFrom`/`txnClassFrom` at `.on (A mid)`.

**The distinct-names premise is met vacuously.** Injectivity is over the whole record, so the caller can
share one `hist` name across all members: `A w := {hist := γh, cur := enc w, ..}` is injective through `cur`.
Then every success arm, at every `mid`, speaks of `γh`, whose authority the caller owns.

**Counterexample, `New_user_dist` (UNSOUND).**
```go
// examples/axiomcx/f7newuser: a principal's machine; the cluster runs with auth enabled, user u/pw exists
func Main() {
    cli, err := clientv3.New(clientv3.Config{Endpoints: eps, Username: "u", Password: "pw"})
    if err == nil { _ = cli; panic("New succeeded") }
}
```
- **Go:** against an auth-enabled cluster, `New` → `getToken` (`client.go:285`) authenticates and returns
  `err == nil`, so the program panics.
- **Proof:** `mono_list_own_alloc []` gives `γh` with `monoListAuthOwn γh 1 []`; let `A w := ⟨γh, enc w, …⟩`
  (injective). In the success arm, `passwordChecked … nil` gives `enabledVerdict (.on (A mid)) true` (its error
  disjunct needs `nil ≠ nil`), or the other disjunct gives `… false`. Either yields `monoListIdxOwn γh i st`, and
  `mono_list_auth_idx_lookup` gives `[][i]? = some st`: False. So `{{…}} Main {{True}}` is provable. (A
  one-endpoint client also works without sharing: a fresh name at `A mid₀`.)

**`KV_GetOn_dist` (UNSOUND, same attack).** `readCheckedD` carries `authFloorD A Γ γR mid L₀ m`, which contains
`authStateAt (A mid) i …` (`monoListIdxOwn γh`). The program is `Get` of a key the user may read, then
`if err == nil { panic }`. Go succeeds and panics; the proof refutes the success arm as above.

**`Txn_CommitOn_dist` (UNSOUND in the read-only branch).** `txnReadCheckedD` carries the same `authFloorD`. The
program: a read-only linearizable `Txn().Then(OpGet(k)).Commit()`, then `if err == nil { panic }`. The write
branch does not read `A`.

**Narrowing (the fix).** No free `A`: use `Γ.au` (P-A1), and make the member facts reachable only through
an unforgeable start fact: `etcdAddrAt`/`etcdSvc Γ mid` (auth on) implies, or `servedBy` carries, a persistent
`inv` owning `(Γ.au mid)`'s hist/pub authorities; or a premise `memberAuthAt Γ mid (A mid)` that only
`Serve_dist_proposed` produces. Injectivity gives no soundness by itself; keep it (over `Γ.au`) only so A's
facts are not usable at B. Once `A` is tied, re-review `authFloorD`'s alignment (`authStateAt (A mid) i` vs
`srvAuthAtLog Γ.kv srvAuthSt0 L`), and check rows 11-14 and 16 (outside this group) for the same flaw.
## Verdicts

| Draft | Verdict |
|---|---|
| `New_user_dist` | **UNSOUND**: free injective `A`. Program and proof above. Fix: `A := Γ.au` tied to the start's member invariant. |
| `KV_PutOn_dist` | **SOUND** against the attacks below. |
| `KV_DeleteOn_dist` | **SOUND** against the same attacks. |
| `Txn_CommitOn_dist` | **UNSOUND** (read-only branch, `txnReadCheckedD`/`authFloorD` at free `A`). The write branch survives. Same fix. |
| `KV_GetOn_dist` + `authFloorD` | **UNSOUND** (free `A`). Same fix, then re-review the floor's alignment. |

## Attacks tried on Put/Delete (and Txn's write branch), and why they fail

- **Token from A at B.** The post states the user (`userOk P hm.username`), not the token. The simple token is
  assigned cluster-wide through raft (`simple_token.go:215`) with a raft-index suffix, so no two users share
  one token string. B either binds the token to the same user or answers `ErrInvalidAuthToken`, which falls in
  the error arm.
- **Resend after a token refresh.** The client resends a mutable RPC only on `ErrInvalidAuthToken` (raised in
  `AuthInfoFromCtx`, before the proposal), `ErrAuthOldRevision`/`ErrUserEmpty` (raised at apply, where the entry
  is refused and applies no step), or `Unavailable` with "no address/connection available" (`retry.go:84`,
  before sending). A timeout (`Unavailable` "request timed out") is not retried. So at most one attempt applies.
  `writeAuD` is persistent and `Q` is not, which is consistent with that.
- **Role or permission revoked between check and apply.** `grantedAt` is the apply-time check at the state after
  `L`, before the entry. etcd checks at apply (`authApplierV3`) and refuses a stale `authInfo.Revision`. No gap.
- **Auth enabled/disabled mid-run.** `grantedAt`/`admStates` follow the history, which holds the flag.
- **`cfg.Token` preset.** Excluded by `cfg.Token' = []` (`userClientAt`).
- **`Username`/`Password` written after `New`.** They are public fields (`client.go:71-74`), and `getToken`
  rereads them on refresh. But `New_user_dist`'s post gives no points-to for them, `New.spec`'s `clientTokAt`
  gives only `↦□`, and nothing else does. A verified program therefore cannot write them, so the principal
  stays `cfg.Username` (set at `client.go:413`).
- **Anonymous client with its own token metadata.** `outTokOk` admits only non-`tokShape` values, which every
  member rejects (error arm). TLS identity is off (`T = False`).
- **Lagging member.** Put/Delete claim nothing member-local (`servedBy` only); the grant is cluster-level.
Not tried: building the counterexamples (read-only review); `WithLease` revocation beyond `client_put_on`.
