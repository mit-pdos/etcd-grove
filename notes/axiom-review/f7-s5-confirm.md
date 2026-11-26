# F7 S5 fixes: confirming review (2026-11-26)

This review used the `axiom` skill and was read-only. It read `/shared/etcd-grove-f7` at `26cdaf49f7` (branch
`etcd-safe-f7`; the fixes are `1b320c387a`, `f6d33a2204` and `708c342561`) and wrote nothing there. The Go source is
the etcd pin in `/shared/tmp/coord-03/f7-s5-gotest/etcd`, with grpc v1.84.0 and go1.27.3 (`GO_TOOLCHAIN`).

## Verdicts

| target | verdict |
|---|---|
| 1. The new `outTokOk` (13 contracts) | **SOUND. The previous attack is closed.** Every way Go binds a caller to an issued token goes through `token` or `authorization`, after a `Bearer ` trim. The new premise forbids that for `P = none`, and for `P = some u` it allows no added token key at all. It is stricter than the server in two places: it checks every value, where the server reads only `ts[0]`, and it checks both keys, where the server reads only the winning one. That costs completeness, not soundness. |
| 2. `authFloorD`'s update | **MATCHES `akAuthFixed`.** The form is the same: `□ ∀ E', ⌜authTieReadMask ⊆ E' ∧ i ≤ j⌝ -∗ authStateAt … ={E'}=∗ …`, a mask-preserving update at any mask holding the tie's namespaces. A caller can fire it inside a WP step, at `⊤` or at any mask that still holds `authTieReadMask`. `authFloorD_frozen` does this, and it opens `kvN` and `authHistN` afterwards at the same `E`. The R1 derivation (`authTieN`, `authRev`, then `srvReqLogLb_of_rlogLb` at `srvRaftN`) uses only namespaces inside `authTieReadMask`. |
| 3. The re-proved callers | **OK.** Every discharge is `outTokOk_none` at `om = none` or `outTokOk_reqMd`. The callers are `absent`, `grantPut` (twice), `barrier`, `SetUpDist:86`, `noAuth` and `foreign`. Each `om` is tied to the real context by the contract's own `metadata.outMD ctx om` premise, which Lean checks. The Go matches: the only metadata the example clients add is `reqCtx("bad")`'s `token: badtoken` (`authlease.go:30`). No client adds `authorization`, and the dial options are only `grpc.WithNoProxy()` (`auth.go:37`). The contracts require that through `kvClientAt`'s and `authClientAt`'s `clientNoProxy`, so no per-RPC credential can inject a key. |

## 1. `outTokOk` against the server

The server code is `AuthInfoFromCtx` (`server/auth/store.go:1072-1097`):

```go
ts, ok := md["token"]; if !ok { ts, ok = md["authorization"] }
token := strings.TrimPrefix(ts[0], "Bearer ")
```

The simple provider accepts only tokens it has assigned (`simpleTokens[token]`, behind `isValidSimpleToken`'s
`x.<uint>` split). Every assigned token is `fmt.Sprintf("%s.%d", prefix, index)`, which is `tokShape`.

The checklist:

| question | Go (test below) | `outTokOk` |
|---|---|---|
| Both keys present: which wins? | `token` wins, whatever the append order (`token=alice, authorization=root` binds alice: RoleList denied, Put(z) denied). | It constrains both keys. Sound either way. |
| `Bearer ` trimming | Exactly one, case-sensitive `"Bearer "`, on whichever key wins, `token` included. `Bearer <root>` is accepted under both keys. `bearer `, two spaces, `Bearer Bearer ` and a leading space are all rejected. | It checks `tokShape (trimPrefix t "Bearer ")`, the same single trim the server applies. `auth.mdTokenOf` (`InvAuth.lean:734`) models the same reading. |
| Several values per key | The server reads only `ts[0]`: `authorization=[root, bad]` binds root, and `[bad, root]` is refused. | It checks every value, which is stricter. |
| The empty string | `token=""` still wins and is refused (`invalid auth token`), even with `authorization=root`. `authorization=""` is refused too. | `tokShape ""` is false (a simple token contains a `.`), so an empty value is allowed only for `P = none`, which is right. |
| A key with an empty value list | `NewOutgoingContext(MD{"token": {}})` plus `authorization=root` binds root: grpc sends no header for an empty list, so `authorization` wins. | `mdVals om "token" = []`, so the first disjunct needs `authorization` empty too. The second disjunct checks `authorization`'s values. Sound. |
| Key case | grpc lower-cases keys. `Append("Authorization", root)`, `Append("TOKEN", root)` and a raw `NewOutgoingContext(MD{"Authorization": …})` **all bind root**. | `mdVals` looks keys up literally, so an upper-case key would evade it. But no spec can produce one: `AppendToOutgoingContext.spec` requires `metadata.lowerKey k`, `NewOutgoingContext` has no spec, and `withVersion`/`WithRequireLeader` set fixed lower-case keys (`client-api-version`, `hasleader`). Sound within the model. This rests on that premise. See "Residual". |
| `authorization-bin` | It is not read (`user name is empty`). | Not a token key. Correct. |
| The client's own credentials | A per-RPC `token` is sent before the context's metadata (`http2_client.go`: `authData` before `md`), so the client's token wins: alice's client with `token=root` added is still alice. | `P = some u` must use the first disjunct (no added key), so this ordering is never relied on. An anonymous client (`principalOf = none`, `cfg.Token' = []`) has no `authTokenBundle` (`client.go:413-422`), so it sends no credential. |
| The gRPC gateway | It forwards HTTP `Authorization` as `authorization`, the same key. | Not reached. The contracts are `clientv3` gRPC calls, and the dist deployment runs `etcdserver.NewServer`, not `embed`'s gateway. |

**The previous attack, rerun:**
- The attack was an anonymous client (`P = none`) sending root's token under `authorization`, with or without `Bearer `.
- `mdVals om "authorization" = [tok]`, so the first disjunct fails.
- The second disjunct needs `¬ tokShape (trimPrefix tok "Bearer ")`, but the trim gives root's issued token, which is `tokShape`. So `outTokOk none om` is false, the contracts cannot be applied, and the counterexample program has no proof.
- The same holds for every variant in the test that Go accepts.

### The test: `/shared/tmp/coord-03/f7-s5-gotest/etcd/tests/integration/f7s5_confirm_md_test.go`

**Setup:**
- A one-member cluster with auth on (simple tokens), root, and `alice` (read-write on `[a,b)`).
- An anonymous client calls RoleList (admin only), `Put a1` (alice or root) and `Put z` (root only), with an 8s timeout per call. This tells root, alice and refusal apart.

**Result:** `--- PASS: TestF7S5ConfirmMetadata (61.54s)`. The full log is `f7-s5-gotest/confirm-output.txt`.

```
none                                         empty / empty / empty
token=root                                   ok / ok / ok                   (root)
authorization=root                           ok / ok / ok                   (root)
token=alice, authorization=root              denied / ok / denied           (alice: token wins)
authorization=root, token=alice (swapped)    denied / ok / denied           (alice)
token="", authorization=root                 invalid x3
token=badtoken, authorization=root           invalid x3
authorization=[root, badtoken]               ok x3                          (ts[0])
authorization=[badtoken, root]               invalid x3
token=[alice, root]                          denied / ok / denied           (ts[0] = alice)
authorization="Bearer "+root                 ok x3
token="Bearer "+root                         ok x3                          (trim on token too)
authorization="bearer "+root                 invalid x3
authorization="Bearer  "+root (2 spaces)     invalid x3
authorization="Bearer Bearer "+root          invalid x3
authorization=" "+root                       invalid x3
authorization=""                             invalid x3
Append "Authorization"=root                  ok x3                          (lower-cased by grpc)
Append "TOKEN"=root                          ok x3
NewOutgoingContext MD{"Authorization": root} ok x3                          (raw upper-case key delivered)
NewOutgoingContext MD{"authorization": root} ok x3
NewOutgoingContext MD{"token": {}} + authorization=root   ok x3             (empty list not sent)
authorization-bin=root                       empty x3
alice client + authorization=root            RoleList denied                (creds' token wins)
alice client + token=root                    RoleList denied
```

### Residual (not a defect today)

The soundness of `outTokOk` against key case rests on there being no spec that lets a program put an upper-case or
mixed-case key in its outgoing metadata. Today `AppendToOutgoingContext.spec` requires `lowerKey`, and there is no
spec for `NewOutgoingContext`, `metadata.Pairs` or `MD.Set` on a raw map.

If such a spec is added later, `outTokOk` (and `mdTokenOf`, the server-side reading) must compare keys after
`ToLower`, or that spec must also require `lowerKey`. The test above shows grpc delivers a raw `"Authorization"` key
as `authorization`. I suggest putting one line about this in `outTokOk`'s docstring.

## 2. `authFloorD`

The new text (`AuthViewDist.lean:199-205`):

```lean
□ (∀ (E' : CoPset) (j : Nat) (st : auth.AuthState), ⌜authTieReadMask ⊆ E' ∧ i ≤ j⌝ -∗
  auth.authStateAt (Γ.au mid) j st ={E'}=∗
  ∃ L', ⌜L₀ <+: L' ∧ st = srvAuthAtLog Γ.kv srvAuthSt0 L'⌝ ∗ srvReqLogLb γR L')
```

The comparison is `akAuthFixed`, at `examples/etcd/auth/WorkEnv.lean:87`:

```lean
□ (∀ (E' : CoPset) m st, ⌜authTieReadMask ⊆ E' ∧ n ≤ m⌝ -∗ auth.authStateAt γa m st ={E'}=∗ …)
```

They agree on everything that matters:

- **The mask:** the same quantified `E'`, with the same lower bound `authTieReadMask`, which is `srvRaftN ∪ kvN ∪
  authHistN ∪ authTieN ∪ authRev` (`AuthTieRead.lean:47`).
- **The update is mask-preserving**, so a caller can use it inside a WP at `⊤`, or under any mask that still holds
  those five namespaces.
- **It fails exactly where `akAuthFixed` fails:** inside an opened `kvN` or `srvRaftN`, such as inside the AU of
  `KV_GetOn_dist`, whose mask is `(⊤ \ srvRaftN) \ kvN`. That is the intended discipline, not a regression.
- **The way it is used:** `authFloorD_frozen` (`AuthFrozenFloor.lean:56`) takes `authTieReadMask ⊆ E`, fires the
  update at `E`, and then opens `kvN` (`authHistLb_of_reqLogLb`) and `authHistN` (`authHistFrozen_prefix`) at the
  same `E`. `leaseCheckD_none_frozen` consumes the result at `E`.
- **It can be derived:** the R1 derivation needs `authTieN` (read the cap's `A`), `authRev` (`authStateAt_capped`)
  and `srvRaftN` (`srvReqLogLb_of_rlogLb`, `SrvRaftLog.lean:1494`). All three are inside `authTieReadMask`, so the
  form no longer claims more than the server can give.
- **Unchanged:** the `i ≤ j` bound and the content (§2.1 of the previous review: alignment by strict revision
  monotonicity).

## 3. The callers

These are the Lean changes in `1b320c387a` and `f6d33a2204`. The only other change, `708c342561`, is a syntax-only
edit in `foreign`.

- **`outTokOk_none`** replaced `Or.inl rfl` and `by left; rfl` in:
  - `absent.lean:79`
  - `grantPut.lean:87,131`
  - `barrier.lean:100`
  - `SetUpDist.lean:86`

  `mdVals none k = []` holds for both keys by `rfl`.
- **`outTokOk_reqMd`** (`AuthLeaseDefs.lean:40`) is used by `noAuth` and `foreign`. `reqMd "bad"` is
  `mdAdd none "token" badToken`. For `P = none` the proof takes the second disjunct:
  - for `token`: `trimPrefix_badToken` and `simpleTok_ne_badToken`;
  - for `authorization`: `mdVals` is `[]` (the `simp` branch).

  Every other principal gets `none`.
- **What the callers rely on, and why it holds:**
  - **The Go contexts carry no `authorization` key.** In `examples/etcd/dist`, the only `metadata.` call is
    `authlease.go:30`'s `AppendToOutgoingContext(ctx, "token", badToken)`. Everything else is
    `context.WithTimeout(context.Background(), …)`.
  - **The clients `New`/`NewClients` build cannot add one.** Their dial options are `[grpc.WithNoProxy()]`
    (`dist/client/auth.go:37`), and the contracts require that through `clientNoProxy` in
    `kvClientAt`/`authClientAt`.
  - **`cfg.Token' = []`** is in `userClientAt` and `authClientAt`.
  - **`om` is the context's real metadata**, through each contract's `metadata.outMD ctx om`, a precondition the
    proofs discharge from the context specs.

  Nothing else is assumed.

## Not done

- **No Lean counterexample was attempted:** the fixed premise excludes the attack, and the review was read-only.
- **The full build was not rerun.** I took the fix-targets note's "23 importer leaves, EXIT 0" as given.
