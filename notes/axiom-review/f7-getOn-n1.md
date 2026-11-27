# Re-review: `KV_GetOn_dist` after N1, the per-member tie, and `Lease_TimeToLiveOn_dist` (2026-11-26)

`axiom` skill, read-only. Branch `etcd-safe-f7` @ `e4f694575f` (read through `git show`); the `TimeToLiveOn`
draft is read from the uncommitted working tree of `/shared/etcd-grove-f7` (2026-11-26). Go: `.lake/go-src/etcd`
(the fork at the pin). No Go test and no Lean proof were written, so the attacks below are shapes.

## Verdicts

| target | verdict |
|---|---|
| 1. `etcd_dist.authd.KV_GetOn_dist.wp_proof` with N1 applied (`readCheckedD` gives `srvReqLogLb γR L`) | **SOUND**. No counterexample found. The new claim goes past the in-process post; it should follow from the member's tie (retirement obligation R1) |
| 2. The tie of `Γ.au mid` / `Γ.ls mid` through the adopted `Serve_dist` + `NewServer.specG_dist` | **HOLDS**. Condition C of `f7-rerev-a.md` is now met by the adopted texts, not vacuously |
| 3. `Lease_TimeToLiveOn_dist` (generalized draft, any options) | **SOUND as drafted**. The draft claims nothing about `TTL`, `GrantedTTL` or `Keys`, and that must stay so: see 3.3 for the reply claims that would be false |

## 1. `KV_GetOn_dist` with N1

**The new claim.** A success gives a committed requested prefix `L` with `L₀ <+: L`, and the user may read
`[key, e)` at `srvAuthAtLog Γ.kv srvAuthSt0 L` (`readAuthedD`). It also gives `srvReqLogLb γR L`, so `L` is
a prefix of the **committed** log of requested entries (`srvLogCore`; `f7-rerev-a.md` §2).

**What Go does** (`v3_server.go` `Range` → `linearizableReadNotify` → `doSerialize:1036`):
1. The read barrier waits until the member's applied index is at least the read index, which is at least every
   commit before the call.
2. Then `AuthInfoFromCtx` reads the token's user and the auth revision.
3. `IsRangePermitted` → `isOpPermitted:862` checks against the member's current store: enabled, revision, the
   user record and the range-permission cache.
4. After `get()`, `ai.Revision != Revision()` → `ErrAuthOldRevision`.

So the passing check ran against a state the member's apply thread recorded at an index `j`. Each such state is
the history state of a committed log: `authHistTie` is in `isServerReadM true` (`isServerReadM_tie`,
`ReadOn.lean:878`). Its cap is `bootState :: admStates ρ.kv st₀ A` for a committed `A`, and the store's history is
a prefix of the cap (`authOwn_capped`). So `j` is a position in that history at or after the floor's index `i`.
The floor's state there is `srvAuthAtLog L'` with `L' ⊒ L₀` (`authFloorD`).

Choosing `L`:
- `j`'s state is the floor's: take `L := L'`.
- Otherwise: take the prefix of `A` up to the admin entry that produced position `j`. It extends `L'`.

Either way `L` is committed, `L ⊒ L₀`, and the verdict's `permitted` holds there. Since `permitted st _ = st.enabled
= false ∨ granted …` (`auth/Model.lean:204`) and `rv` is free, the cluster-level `readAuthedD` holds.

**Attacks tried:**

- **Lagging follower, linearizable.** Blocked: the barrier forwards `ReadIndex` to the leader and waits until
  applied ≥ read index. The fork's raft has the single-voter read-index fix. A deposed leader cannot pass
  `ReadOnlySafe`'s quorum round. So the member's state is at least the state after `L₀`.
- **Serializable read on a lagging follower.** This *would* refute the claim. Shape: the admin revokes the user's
  read permission and the client holds the committed `L₀` that includes the revoke. In Go, a serializable `Get` at
  a follower that has not yet applied the revoke succeeds, because no barrier runs. A proof would derive `False`:
  every committed `L ⊒ L₀` denies the read, given a frozen history in which nothing re-grants it. The premise
  `(rangeWireOf …).base.serializable = false` excludes this, so **the premise is load-bearing** and must stay.
  `KV_Get_dist` (auth off) allows serializable reads but claims nothing about auth (its `Q` is `True` then), so
  the two are consistent.
- **Revision compacted away.** `Range` returns `ErrCompacted`, which falls in the error arm. N1 does not touch the
  KV part (`σ`, `srvRangeOk`), which is unchanged since `f7-rerev-a.md`. The new `L` is not tied to `σ`, so N1 adds
  no claim relating the auth prefix to the read revision.
- **Mid-apply view.** `commitRevision` runs before `refreshRangePermCache` (`store.go:577-578`, ...), so a check
  can see the new revision with the old cache. That is the state one entry earlier, still at or after the read
  index. A stale revision makes the trailing check fail. Either way the in-process `permVerdictFrom`
  (`FreshCheck.lean:107`) already states the verdict at a recorded state, which the derivation above uses. This
  rests on the in-process auth proof; it was not re-audited here.
- **Wrong user.** The principal cannot be swapped:
  - `outTokOk` and `cfg.Token' = []`: the only token sent is `New`'s, for `cfg`'s user.
  - TLS common name: `□ (srvTLSId s -∗ False)` in `memberUpOnL`.
  - Simple tokens are assigned at apply to the same user on every member.
  - An anonymous caller (`P = none`) gets `ErrUserEmpty` when auth is enabled, and `userOk none` forces the empty
    user, so only `enabled = false` at `L` can make `readAuthedD` hold. That matches Go.
- **Restarted member answers with an old state.** It cannot: `NewServer.specG_dist` requires a fresh WAL
  (`wal.bootRes`). A restarted member cannot meet `memberUpOnL` at the old `Γ.au mid` (`f7-rerev-a.md` residual).

**Against the in-process contract.** `v3rpc.rangeAuthed` (`ServerKVOn.lean:162`) gives `rangeClassFrom` at `m`
and `authFloorAt`, but no committed `L` for the permitted state. The dist post is therefore **stronger** than the
in-process post. It is true of Go by the tie argument above, but it is not yet a corollary of a proved lemma.

**R1 (retirement obligation, new).** Prove a lemma:

> from `authHistTie E ρ srvAuthSt0`, `authStateAt γa i (srvAuthAtLog L')`, `i ≤ j` and `authStateAt γa j st`,
> derive `∃ L ⊒ L', srvReqLogLb ρ.raft L ∗ ⌜st = srvAuthAtLog L⌝`

This is the generalization of `authStateAt_setup`, `AuthTieRead.lean`, via `srvReqLogLb_of_rlogLb` and
`kvRaftOfOn_eqv`. Add it to the axiom's docstring next to the obligations already listed in `f7-rerev-a.md` §2.

**Precision (optional, not soundness).** `readAuthedD`'s `user` is not tied to `info.Username'`; the two
existentials are separate. Tying them would be truthful but adds nothing a client needs today.

## 2. The tie of per-member names

The adopted texts:
- `Serve_dist.spec` (`Spec/.../dist/ServeDist.lean`), auth on: takes `memberUpOnL s ρ E₀ lg γn mid (Γ.au mid)
  Γ.kv.lm (Γ.ls mid)`, `kvCongr ρ.rd.kv Γ.kv`, `ρ.rd.kv.hist = Γ.kv.hist` and `etcdAddrAt a Γ mid`.
- `memberUpOnL` (`MemberLessor.lean:149`) contains `E.authMode = .on γa` and `mvccLeases E.γ = γl`, plus
  `isServerReqM true s E …`, `isServerReadM true s E ρ.rd` and `srvAuthLb s E`. These come only from
  `NewServer`'s post.
- `NewServer.specG_dist`: `γa` and `γl` are now the caller's.
  - Premises: `Hγa` (`authNamesFreshD γa`, exclusive, auth on) and `Hlslot` (half the lessor authority plus the slot).
  - Post: `on = true → E.authMode = .on γa` and `mvccLeases E.γ = γl`.

This matches the proposed text that `f7-combined.md` reviewed (SOUND).

Consequences:
- A served auth-on member at `(Γ, mid)` is a real server whose auth store is at `Γ.au mid` and whose lessor is at
  `Γ.ls mid`. Its read invariants (`srvRaftLogInv ρ.rd.raft`, `kvInvOn`, `authHistTie`) are at KV names that are
  `kvCongr` to `Γ.kv`: `rlog`, `c0`, `ch0` and `log0` are equal. So `srvReqLogLb γR` (with `γR.raft.log =
  Γ.kv.rlog`) and `srvAuthAtLog Γ.kv srvAuthSt0` in the dist posts are the member's own.
- `etcdSvc` has no law and `Serve_dist` is the only server of it (`f7-combined.md` §3). The fake-names attack
  (`f7-a.md`) stays closed:
  - `authNamesFreshD` and the lessor half are exclusive, so names the prover chose cannot get an answering server.
  - The two modes cannot be confused: `.on γa` against `E.authOn = false`.
- `NewServer` does not tie `γa` to the raft `id`. This does not matter for soundness: what the drafts use is
  "the server answering at an address of `(Γ, mid)` has auth names `Γ.au mid`", and `Serve_dist` states exactly
  that. Every draft also takes the injectivity premises.

Missing links L1–L5 of `f7-combined.md` (no auth-on start path) are usability gaps only, not soundness gaps.

## 3. `Lease_TimeToLiveOn_dist` (generalized draft)

**The draft.** The success arm is the echoed `ID` plus
`leaseCheckD (Γ.au mid) P n (fun info => if leaseKeysFold gs false then leaseKeysVerdictFrom … else
⌜P = some info.Username'⌝)`, at `n ≥ n₀` and `j ≥ m₀`. The error arm is unchanged.

**Go** (`v3_server.go:697-720`; `v3rpc/lease.go:62-76`; `client/v3/lease.go:246`):
- `requireAuthInfo:1278` runs first, whatever `r.Keys`: auth disabled, or a non-nil `AuthInfo` (otherwise
  `ErrUserEmpty` or the token error).
- With `r.Keys` only: `checkLeaseTimeToLive:608` at the receiving member over its own lessor, then the trailing
  revision check.
- Then `leaseTimeToLive` is answered by the leader's lessor (locally if leader, else over `leasehttp`).
  `ErrLeaseNotFound` becomes a **success** reply in `LeaseServer` with `ID: rr.ID, TTL: -1` and no keys.
- The client copies `resp.ID`.

### 3.1 The no-keys arm (`r.Keys = false`)

- `ID ↦□ id`: true on every success path. This includes the not-found path (`ID: rr.ID`) and the forwarded path
  (`lreq.LeaseTimeToLiveRequest.ID`, `http.go:131`).
- `leaseCheckD … (fun info => ⌜P = some info.Username'⌝)`:
  - Auth disabled at the member: `requireAuthInfo` returns `nil` at the current state, whose index is at least the
    published `n₀`, so the `enabledVerdictFrom … false` disjunct holds.
  - Auth enabled: the info comes from the token the member accepted. There is no TLS fallback
    (`□ (srvTLSId s -∗ False)`). By `outTokOk` and `cfg.Token' = []`, the only token is the one `New` obtained for
    `cfg.Username`. Simple tokens map to the same user on every member, so `info.Username' = cfg.Username` and
    `P = some …`.
  - Anonymous caller (`P = none`): Go never passes `requireAuthInfo` with auth enabled (`ErrUserEmpty`, or
    `ErrInvalidAuthToken` for an unshaped token), and the draft allows success only through the disabled
    disjunct. This matches.
  - Using `principalOf cfg = some info.Username'` instead of `userOk` is correct: `userOk` would admit the empty
    user, which Go refuses.
- `authPubLbM n`, `lessorLb j`: trivially satisfiable (`n = n₀`, `j = m₀`). Harmless.

### 3.2 The keys arm

It is unchanged from `f7-rerev-c.md` (SOUND given the tie, which §2 confirms). Its key point holds: the verdict is
the receiving member's (its own lessor, `Γ.ls mid`), and the post says nothing about the reply's keys. Two known
Go bugs show why it must not:
- `issues/etcd-lease-timetolive-keys-toctou.md`: the keys are read after the check.
- `nonissues/etcd-lease-checks-lagging-member.md`: a lagging member checks an absent lease vacuously, then the
  leader returns its keys.

### 3.3 The intended "no keys" reply and `ttl = -1`: what would be true

The draft states none of this today. If a reply claim is added, Go supports only the following.
- **`Keys` empty without `WithAttachedKeys`: true** on every success path. `resp.Keys` is set only `if r.Keys`
  (`v3_server.go:652`, `http.go:136`), the not-found reply sets no keys, and protobuf decodes an absent repeated
  field as nil.
- **`Keys` with `WithAttachedKeys`: only "some list".** It is the leader's lessor's keys at its own lookup, not
  `Γ.ls mid`'s and not checked. It must not be tied to `leaseKeysVerdictFrom` or to member `mid`'s lessor.
- **`TTL = -1` for an unknown lease: only as "not in the answering primary's lease map".** That is not a fact
  about `Γ.ls mid`, and not a linearizable fact about the committed log:
  - A newly elected leader's `ApplyWait` waits only for its own committed index.
  - A partitioned, deposed leader still answers as primary (`Demoted()` is false until it steps down).
  - So a lease revoked by a committed entry can still be reported alive, and a lease granted by a committed entry
    can still be reported `-1`.
- **`TTL = -1` for an expired lease: FALSE.** An expired lease that is not yet revoked (the revoke is still being
  proposed, or the leader cannot commit) stays in the map. `TTL = int64(l.Remaining().Seconds())` with
  `Remaining = time.Until(expiry)` (`lease.go:117`) is truncated toward zero: 0 for up to 1 s overdue, then
  -1, -2, .... So an expired lease answers 0 or any negative number. Conversely, `TTL = -1` does not imply the
  lease is unknown (it can be 1–2 s overdue).
- **Safe reply shape, if one is wanted:**
  > `ID = id`, `Keys = []` when `¬ leaseKeysFold gs false`, and `TTL = -1 ∧ GrantedTTL = 0 ∧ Keys = []`
  > ∨ (any `TTL`, any `GrantedTTL`)

  This is view-free, like F2's `Lease_TimeToLiveKeys_dist`. Anything tying `TTL` to the expiry or the
  revocation of a lease in `Γ` needs a leader-side contract, which these axioms do not have.

**Verdict:** the draft as written is sound (its success arm claims only the ID and the member-local check). Keep
the reply's `TTL`/`Keys` out of it, or add only the safe shape above.

## Not tried

- No Go tests or Lean counterexamples: no candidate survived reading.
- Not re-audited:
  - the in-process auth store's `permVerdictFrom` proof chain (whether it rests on axioms of its own);
  - the KV half of `KV_GetOn_dist` (reviewed in `f7-rerev-a.md`);
  - the other 12 F7 axioms (unchanged, `f7-changed-since-review.md`).
