# F7 review, group B: the auth admin drafts (`AuthViewDist.lean` @ `d946f6cbda`)
Read-only review (`axiom` skill, attack-by-program; no Go/Lean counterexample built, since no attack reached
a client-side panic). Read: the five drafts (`AVD:407-515`), `adminRepliedD`/`userOk`/`outTokOk`/`authClientAt`,
`histAu` (`ProposeOn.lean:435`), `adminDoneM` (`ReqOn.lean:252`), `adminQh`/`adminRecRes`, the mirrored
`etcd*SpecW` (`v3rpc/AuthService.lean`), `authClient.*.spec`, `isNewClient`/`clientAuthAt`/`retryClientOk`; Go:
`client/v3/{client,retry_interceptor}.go`, `server/auth/store.go`, `server/storage/backend/batch_tx.go`; the driver
(`examples/etcd/auth/authkv.go` `SetUp`, `examples/etcd/dist/client/auth.go`).

## Verdicts

| Draft | Verdict |
|---|---|
| `Auth_UserAdd_dist` | **NEEDS-FIX** (missing name bound, below) |
| `Auth_UserGrantRole_dist` | SOUND |
| `Auth_RoleAdd_dist` | SOUND |
| `Auth_RoleGrantPermission_dist` | SOUND |
| `Auth_AuthEnable_dist` | SOUND |

## The fix (UserAdd)

`Auth_UserAdd_dist` drops the server's premise `name.length ≤ backend.maxKeySize`, which the spec it mirrors
asks of the caller (`etcdUserAddSpecW`, `AuthService.lean:121`) and which the three sibling drafts keep
(`AVD:443`, `:464`, `:487`). A name over 32768 bytes passes the client (`strsSizeOk` allows 2^30) and the
server's `MaxRequestBytes` (1.5 MiB). At apply, `UnsafePutUser` makes bbolt return `ErrKeyTooLarge`, and
`batchTx.unsafePut` calls `lg.Fatal` (`batch_tx.go:183`) on every member that applies the entry. The member exits.
That is not a panic, and an exit counts as a safe run under `Robust`, so no panicking program follows: the client
sees the error arm or a timeout. But the history model (`histAu`, `admStates`) treats the committed entry as an
applied `UserAdd`, a state no member reaches, and the restart line replays it into the same `Fatal`. **Narrowing:** add
`name.length ≤ backend.maxKeySize` to the pure precondition (`⌜strsSizeOk [name, pw] ∧ name.length ≤
backend.maxKeySize⌝`). The driver meets it ("root", "u", "v"). Style point, not soundness: the update is `(∀ um, ⌜…⌝
-∗ histAu …)` and not the mirror's `□ (∀ um, ⌜…⌝ → …)`. The two are equivalent because the premise is pure and
`histAu` is persistent, but the persistent form matches the mirror and keeps the instance.

## Attacks tried (all five unless noted), and why each fails

1. **Lost reply, then a retry.** The interceptor does not resend a mutable RPC after a context error
   (`nonRepeatable`, `retry_interceptor.go:80`) or after `Unavailable` other than "no address available". It resends
   only after `ErrInvalidAuthToken`/`ErrUserEmpty` (refused before propose) or `ErrAuthOldRevision` (refused at
   apply, no step). So at most one attempt applies a step. A retry by the program: `UserAdd`/`RoleAdd` get
   `ErrUserAlreadyExist`/`ErrRoleAlreadyExist`, which is the error arm, and the first attempt's `□ Q` stays with the
   update and is never handed to the caller. `UserGrantRole` gets the duplicate grant: a success with no
   `commitRevision`. `RoleGrantPermission` replaces the same permission, and `AuthEnable` on an enabled store returns
   nil. These successes carry `adminDoneM` at the retry's own prefix and `adminRecRes`, whose `Q` is conditional
   (`admRec … ∨ ¬ admRec`), so the post claims no second history step. The setup driver retries nothing: a failed step ends `SetUp`.
2. **`AuthEnable` with no root user, or root without the root role.** `store.go:284-291` returns
   `ErrRootUserNotExist`/`ErrRootRoleNotExist` from apply, so the response carries an error, which is the error arm.
   The success arm needs `adminDoneM true …` (`adminStepOk` at the state of `L`), which these refusals do not give.
3. **Admin calls after auth is on, by a non-root or anonymous user.** The header user is whatever the token binds
   (`""` with no token). `histAu`'s `Gb` only restricts it to `userOk P`. Admission is `auth.adminOk` at the last
   state, so the entry is refused at apply and the call takes the error arm. The anonymous client cannot borrow a
   token: `outTokOk` with `P = none` admits only `token` metadata that `tokShape` rejects, and a user client must send
   no ctx token at all. Rewriting `cli.Username`/`Password` after `New` so that a refresh authenticates as root is
   blocked in the logic: `getToken` reads them through `clientAuthAt`'s `↦□` (`InvClientAuth.lean:137`), and nothing
   in `authClientAt` gives a full points-to. The `cfg` field is `↦□` as well.
4. **Concurrent admin calls through different members.** Raft orders them. Each success's `L` is the requested prefix
   before its own entry, and `histAu` fires once per recorded entry at that entry's prefix. No claim compares two calls.
5. **Success versus a lagging member.** The success arm makes only cluster-level claims: `srvReqLogLb γR L` (which
   reads only `γR.raft.log`, `SrvRaftLog.lean:438`, so quantifying over `γR` is harmless), `adminDoneM` at the
   model of `L`, and `adminQh`. The mirror's `pubAfterM` is dropped, so nothing says any member, `mid` included, has
   published the state. `servedBy` is only an address fact. The member that replies has applied its own entry
   (`w.Wait`), and other members may lag; the post claims nothing about them. The drivers' later reads get that
   member state from `barriers`, not from these posts.
6. **A token from member A used at member B, and expired tokens** (only for `P = some u`; the driver's admin calls
   are anonymous). B either binds the token to the same user or answers `ErrInvalidAuthToken`, after which the client
   refreshes and resends without any step having happened. No post mentions a token.
7. **Calls the driver makes versus the drafts.** `SetUp` (`authkv.go:299-321`) runs `UserAdd(root|u|v)`,
   `UserGrantRole(root,root)`, `UserGrantRole(u,r)`, `RoleAdd(r)`, `RoleGrantPermission(r, lo, hi, READWRITE)` and
   `AuthEnable` through the anonymous `cli` while auth is off. Each call has a draft. Every premise is met: the name
   bounds, `key.length < 2^63-1`, and `outTokOk` (no metadata). `UserGrantRole` to the `root` role skips the role
   lookup (`store.go:554`), which is the model's case and not the axiom's.
8. **RoleGrantPermission corner cases.** An arbitrary `permType`, `rangeEnd = "\x00"`, or an invalid range
   (`ErrInvalidAuthMgmt`) are all decided at apply by the proven model (`adminStepOk`), so a refusal takes the error
   arm. The key and rangeEnd are stored in the role's value, not as a bbolt key, so no `Fatal` occurs. The role-name
   bound is kept.

## Not tried

Whether the proven server model (`adminStepOk`, `admRec`, `authDet`) is sound; the cross-machine ghost sharing that
lets a remote apply fire the client's `histAu` (design §18.4, #24 S2: the reason these are axioms); `UserAdd` with
an empty password and `NoPassword = false` (a question for the model, not these drafts).
