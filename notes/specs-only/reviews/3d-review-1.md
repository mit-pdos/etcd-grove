# Batch 3d (auth store, bcrypt boundary): review round 1 (provability and completeness)

Reviewer: independent agent, 2026-11-09. Commit under review: `74a953bc71` (3d's draft). `HEAD` is now
`5b6e94787c`, and 3d's files are unchanged since `74a953bc71`. W0's `Model.lean`/`State.lean` have
**uncommitted** edits in the worktree. They answer some of 3d's requests (`roleGet "root"`,
`pwHash`/`pwMatch`, `validPerm`, `invertedDeny`, `tokenUser_agree`, `pwHash_match`). I judge against
the committed W0 text, and I mark where the working tree changes the verdict.

Go sources: `.lake/src/server/auth/{store.go,range_perm_cache.go,simple_token.go,nop.go}`, and
`golang.org/x/crypto@v0.57.0/bcrypt/bcrypt.go`.

## What is good

- **The four views are modelled faithfully.** I checked `checkPost`/`adminPost` against the locking
  in `store.go`:
  - the flag is read under `enabledMu` (`store.go:965-969`);
  - the revision is an atomic (`:1012-1022`);
  - the backend is read through `lockedReadTx` under `beMu` (`:956-962`);
  - the cache is read under `rangePermCacheMu` (`range_perm_cache.go:110-127`).

  An admin step moves the views in this order: atomic bump, cache rebuild, batch `Unlock`. In
  `AuthEnable`/`AuthDisable`/`Recover` the flag moves last under `enabledMu.Lock`. So each view is at
  a recorded state at or after the reader's bound, which is exactly what `checkPost` says. Every
  error path matches:
  - With the user missing in the backend, the code returns `ErrPermissionDenied` without reading the
    cache. The prover then picks `jc := jx`, and `checkDenied` holds.
  - A cache entry is absent only for an absent user.

  I found no lock-order deadlock either. The reader holds `readTx.RLock`, then
  `rangePermCacheMu.RLock`. The writer takes `rangePermCacheMu.Lock` inside the batch lock, and
  writes back under `readTx.Lock` only after releasing the cache lock.
- **A pass is justified at one recorded state.** `checkOk`'s three disjuncts are each one state's
  `State.permits`. With `authAt_reached`, that is exactly 2b's need for a watch create: "nil only if
  some reached state permits".
- **The writer's checks are exact** (`authCur_at`, `authAt_le`, `authAt_agree`), and `ReqWriterCheck`
  is provable as written.
- **One spec per mode**: there is no `AuthMode`, and the old off-mode axiom is gone.
- **The bcrypt boundary is the right shape.** It assumes correctness only (a hash accepts its own
  password), and that is true at v0.57.0:
  - `GenerateFromPassword` refuses more than 72 bytes (`bcrypt.go:93-95`), replaces a cost below 4
    by 10, and refuses a cost above 31 (`newFromPassword`, `checkCost`).
  - `rand.Reader` never errors on the pinned toolchain.
  - `CompareHashAndPassword` re-hashes under the parsed cost and salt. It does not mutate either
    slice (`append(key[:len(key):len(key)], 0)` copies).
  - No panic. A long password is truncated by `blowfish.ExpandKey`; a hash under 59 bytes is
    `ErrHashTooShort`.

  Nothing claims "a wrong password fails", so there is no false universal.
- **The three nonissues are real findings**, with correct mechanisms (corrections below).
- **The cluster-named store handle (`authStoreAt st γ γa`, open question 4) is acceptable.**
  `tokenUser γ` is cluster-level anyway.

## First tier

### F1. `admStep` is unsatisfiable for every changing step: the admin posts, `Recover`'s premise and `authAt_reach` are false or vacuous (unsound)

`Api.lean:192`:

```lean
def admStep (rq : Req) (a a' : AuthState) (res : Resp) : Prop :=
  ∀ (who : Principal) (σ : State), σ.auth = a → a.mayCall who rq →
    authStep who rq σ { σ with auth := a' } res
```

Since W0's round 4, every changing `authStep` also appends to the history:
- `bump` gives `authHist := σ.authHist ++ [σ.auth]` (`Model.lean:1093` in the working tree; the same
  at `HEAD`);
- `authEnable`'s success does the same (`:1121`).

`{ σ with auth := a' }` keeps `σ.authHist`. So the equation `σ.authHist = σ.authHist ++ [σ.auth]` is
needed, and it is false. Whenever some principal may call (always, at reachable states: auth off,
or `root` with the root role while on), `admStep rq a a' res` holds only for `a' = a`.

Consequences:
- **Every `AdminTriple` spec is false when the code succeeds** (`UserAdd`, `UserDelete`,
  `UserChangePassword`, `UserGrantRole`, `UserRevokeRole`, `RoleAdd`, `RoleDelete`,
  `RoleGrantPermission`, `RoleRevokePermission`), and so are `AuthEnable.spec`/`AuthDisable.spec`:
  their post requires `⌜admStep rq a a' res⌝` with `a' ≠ a`.
- `admNext` becomes vacuous.
- `AuthReach` collapses to `refl`, so `Recover.spec`'s premise `AuthReach a a'` cannot be
  established by 2d for a snapshot that changed auth.
- `ReqAdminSteps`/`ReqRevisionBumped` are "provable" only because the posts are contradictory.

**Fix:** state the store's step on `AuthState`. Either W0 factors `authStep` through an
`AuthState`-level relation (`authStepA who rq a a' res`, with `authStep` its lift that appends
`authHist` exactly when `a' ≠ a`), or 3d defines
`admStep rq a a' res := ∀ who σ, σ.auth = a → a.mayCall who rq → ∃ σ', authStep who rq σ σ' res ∧ σ'.auth = a'`.
F2 suggests the deterministic form.

### F2. `admNext` quantifies over every next state the model allows; 2d can supply it only for the one the cluster reached

`Api.lean:443`, `admNext γ rq a := □ ∀ a' res, ⌜admStep rq a a' res ∧ a' ≠ a⌝ -∗ authReached γ a' ∗ ⌜recordsFit a'⌝`.

Whenever the model's next state is not a function of `(rq, a)`, `admNext` asks 2d for `authReached`
of states the cluster never reached:
- **At `HEAD`, `roleGrantPermission`**: success is allowed for any `perm`, invalid ranges included,
  and the errors are allowed at any state (`Model.lean`, `.roleGrantPermission`).
- **In W0's working tree, `userAdd` and `userChangePassword`**: `∃ cred, pwHash pw cred ∧ σ' = …`
  admits every hash of `pw`.

So `RoleGrantPermission.spec` (and, after W0's edit, `UserAdd`/`UserChangePassword`) cannot be
called by the apply thread.

**Fix:** have the store state what it computes, as a function, and refine W0:
- a transparent `storeStep rq a : AuthState × Resp` (lists in model order; `authRespAt` keeps the
  permutation), with a law `storeStep_adm : storeStep rq a = (a', res) → admStep rq a a' res`;
- `AdminTriple`'s premise about that one state:
  `authReached γ (storeStep rq a).1 ∗ ⌜recordsFit (storeStep rq a).1⌝`.

For the password, the credential must come from the request: `authReqAt r rq` should fix the
decoded hash, for example `rq` carries `cred`, or `storeStep` takes it. The store keeps `decode hp`,
not "some hash of `pw`".

### F3. `RoleGet("root")` with no stored `root` role: `RoleGet.spec` false at `HEAD` (stale once W0's working tree is committed)

`store.go:661-669`: `as.be.GetRole(r.Role)` is consulted first, and gives `ErrRoleNotFound` when no
role named `root` is stored. `rootPerm` is answered only for a stored `root`. Such a state is
reachable even with auth on, because `UserGrantRole` grants `root` without a record
(`store.go:554`: `if r.Role != rootRole`). `AuthEnable` needs only the root user's role list, so no
`root` record is required (`hasRootRole`).

W0 at `HEAD` answers `ok` for `root` whatever is stored. That is also a false client-level
statement, not only 3d's. **W0's working tree fixes it**: `a.roles name = none ∧ res = .err .roleNotFound`
first, and `root` answers a list only when stored. Once committed, this finding is stale.

### F4. The stale-revision race (brief item b): real; NOT admitted by W0's round-4 rule as written; blocks 2c's linearizable reads only

**Real.**
- `commitRevision` bumps the atomic (`store.go:1012-1014`) before the batch transaction's deferred
  `Unlock` publishes the users and roles. `refreshRangePermCache` runs in between, under its own
  lock.
- A simple token's `AuthInfo.Revision` is `as.Revision()` (`simple_token.go:212-221`, via
  `authInfoFromToken`, `store.go:799-801`), and so is a certificate's (`AuthInfoFromTLS`, `:1036`).
- A reader whose `AuthInfoFromCtx` falls in the window takes the new revision. It passes
  `isOpPermitted`'s `revision < rev` test, then reads the user through `lockedReadTx` at the old
  state (root role), or the cache before its rebuild.
- `doSerialize`'s re-check (`v3_server.go:1053`) compares with the same atomic and passes. The read
  in between may see entries applied after the change.

I checked the fork fix the nonissue proposes (bump the atomic after `Unlock`). It closes the race:
- a reader seeing the new revision sees the new backend and cache;
- a reader with the old revision that reads after the publication is refused by the re-check, or
  read before any successor entry was applied.

**W0's rule does not admit it.** The brief describes round 4 as "a read's permission checked at
some auth state reached between `lo` and the answer". That is not what `Model.lean` says. A
linearizable `Range` succeeds only if `σ.permits who … ∨ r.serializable ∨ σ.authOffSince lo`
(`Model.lean:937`; read-only `Txn`: `:979`). `σ` is the answer's state, so with auth on at the
check, success needs the permission at the answer's auth state. The working tree does not change
this. The race gives a pass at the state before the change and an answer after it, so it is not
admitted.

**Where it blocks:** 2c's linearizable `Range`, read-only `Txn` and `RangeStream`. Their sketch
("the revision unchanged means the check's state is the read's", `EtcdServer__Range.lean:20-30`) is
false. It does not block:
- 2b: the watch create needs a reached state that permits, and the check's state is one;
- serializable reads: the model is unconstrained there;
- the lease checks (`v3_server.go:575-601, 608-631`): W0's `leaseRevoke` is re-checked at the apply,
  and `leaseTimeToLive`'s success needs no permission.

**If W0 adopts the brief's reading** (replace `authOffSince lo` by `permittedSince lo who ps :=
∃ j a, lo ≤ j ∧ σ.authTables[j]? = some a ∧ {σ with auth := a}.permits who ps []`, which subsumes
`authOffSince`, since auth off permits), the race is admitted and does not block, given S1's index
link. It would also be one condition instead of two (PRINCIPLES, "No disjunction a proof must
handle twice"). The decision stays the user's: that W0 generalization, or the fork fix. Either way,
2c's sketch must change. The nonissue should say "linearizable" only (see S8).

### F5. `WithRoot` with the simple provider: the panic is real and reachable in etcd's default configuration; `rootTokOk` is sound but leaves the default unserved

- **The panic.** `WithRoot` builds `prefix.0` from a fresh 16-letter prefix (`store.go:1170-1184`).
  `assignSimpleTokenToUser` calls `lg.Panic` if the token is already in the map
  (`simple_token.go:127-141`). The map keeps a token for 300 s, and its TTL is reset on use.
  Nothing else excludes a repeat. Authenticate tokens have index ≥ 1, so only two root tokens can
  collide.
- **The callers.** The leader's lease-expiry loop (`server.go:881`) and the **health checks**
  (`etcdhttp/health.go:222`, `:434`), which the spec's Users list omits. The health checks are
  probed every few seconds by orchestrators, so on the order of 100 root tokens can be alive
  together. The probability is negligible, but it is not zero.
- **The premise.** `rootTokOk` is the only sound premise, and it is correctly placed on the producer
  (`tokenProviderAt tp γ rt`, `NewTokenProvider.spec`'s `rt`). A "probabilistic" premise would be a
  false universal (PRINCIPLES). But 2e's starters set `AuthToken = "simple"`
  (`req/…server_v3_auth.md`, "from 2e, round 1"). So with auth on, every `WithRoot` caller (2d's
  revocations, the health checks' `Range`) has no usable spec.
- **Fix: the fork.** `assignSimpleTokenToUser` returns an error (or `assign` regenerates the prefix)
  on a collision. `WithRoot` already maps an `assign` error to `ctx` (`:1186-1193`), which the spec's
  `ctx' = ctx` arm covers. `rootTokOk` then disappears.

### F6. 3a's exact `opErr` at the writer is not derivable: `checkPost`'s `ErrAuthOldRevision` arm says nothing about the store's revision

- `Api.lean:469`: `err = errOf .authOldRevision ∧ af.enabled = true ∧ rev ≠ W64 0`.
- The code returns it only when `revision < as.Revision()` (`store.go:870-878`).
- 3a's `opErr` (`apply/Api.lean:325-338`) requires `rev < a.rev` for `authOldRevision`, and its
  request (`req/…apply.md`, "from 3a" item 1) asked for exactly that.

At the writer, `authCur_at` makes every view exact, but this arm still admits a refusal at
`rev ≥ a.rev`. `ReqWriterCheck` has to escape it (`!errors.Is(put, ErrAuthOldRevision)`), which shows
the gap.

**Fix:** `err = errOf .authOldRevision ∧ af.enabled = true ∧ rev ≠ 0 ∧ ∃ j a, i0 ≤ j ∧ authAt γa j a ∧ uint.nat rev < a.rev`.

## Second tier

- **S1. The store index ↔ cluster auth-table index link.** `authAt_reached` gives an unordered
  `etcdLb γ σ`. 2c's `lo` arithmetic needs the check's states at cluster index ≥ `lo`:
  `authOffSince`, `deniedSince`, F4's `permittedSince`. `etcdLb_ord` cannot orient an unordered
  witness against the call's anchor. Say who provides it:
  - either 2d (it owns the apply thread and can keep "store index `i` ↔ history point `k`",
    monotone, in its invariant; then `admNext`'s reachedness and `authAt_reached` are 2d's facts and
    the store need not name `γ` at all, which is open question 4's cluster-free option);
  - or 3d, with a law `j ≤ j' → authAt γa j a ∗ authAt γa j' a' ⊢ ∃ σ σ', etcdLb γ σ ∗ etcdLb γ σ' ∗ ⌜σ.auth = a ∧ σ'.auth = a' ∧ Reach σ σ'⌝`
    and an anchor from 2d's `srvApplied`.

  `req/…etcdserver.md`, "from 3d" item 5, leaves this implicit.
- **S2. `Recover.spec` lacks `recordsFit a'`.** At least `a'.rev < 2^64` is needed:
  `Revision.spec` and `AuthInfoFromTLS.spec` claim `uint.nat r = a.rev` at every recorded state,
  `NewAuthStore` and `admNext` supply `recordsFit`, but `Recover` does not. Add it, or add an
  `authBackendAt` law: the stored revision is a `uint64`.
- **S3. `authReqAt`'s pre-3.5 form admits `Password = ""` with `HashedPassword = ""`.**
  `selectPassword` then decodes `""` to an empty slice, without error (`store.go:420-426`). The
  stored credential matches nothing, so `CheckPassword.spec` (no `authFailed` when `p = pw`) is false
  later. `selectPassword.spec` already requires `p ≠ []`; add `pw ≠ []` to `authReqAt`'s legacy form
  (`Api.lean:313-319`).
- **S4. Requests `authReqAt` cannot describe.** A client's `RoleGrantPermission` with a nil `Perm`,
  or an unknown `PermType` (open proto3 enum), reaches the store unchanged (`v3_server.go:973-979`,
  `v3rpc/auth.go:107`). The store answers `ErrPermissionNotGiven` or stores the unknown type
  (`getMergedPerms` ignores it). W0's `Req.roleGrantPermission name perm` has neither. So 3a cannot
  apply `RoleGrantPermission.spec` to them. W0 needs an `Option Perm` (or a garbage form) with
  deterministic errors (also F2).
- **S5. Deterministic answers.** 3a asked for lists "in the store's key order" (`req/…apply.md`,
  "from 3a" item 2); `authRespAt` gives "a permutation". The store's orders:
  - `UserList`/`RoleList`: bbolt key order, a function of the set;
  - `UserGet`: the roles sorted;
  - `RoleGet`: `sort.Sort(permSlice)` by key, unstable, so not a function of W0's list.

  Settle with 2d/3a whether the apply's answer must equal the committed one or be a permutation of
  it. If equal, `storeStep` (F2) must fix the order.
- **S6. The token providers' methods and `permSlice` (the brief's question).** All of these are
  translated with bodies (`Code/…/auth.toml:43-62`) and were verified in the old tree. They were
  proof-internal lemmas there (`Proof/…/auth/TokenSimple.lean`, `TokenSimpleAdmin.lean`,
  `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`), not linked specs: only
  `tokenSimple.genTokenPrefix` was linked (`specs-ref` `Link.lean:1446`).

  So "A smaller API is not a narrower scope" does not strictly force them. But "Canonical specs are
  per (concrete type, method); an interface value gets a bundle … proved once from the concrete
  specs" does: the bundle `tokenProviderAt` presupposes them. Each needs its own (internal) spec:
  - `tokenSimple.info`, `.assign`, `.assignSimpleTokenToUser` (the collision panic: F5), `.enable`
    (starts the keeper: `threadTok`), `.disable` (stops and waits), `.invalidateUser`,
    `.isValidSimpleToken` (waits on `indexWaiter` or `ctx.Done()`). `.genTokenPrefix` has one.
  - `simpleTokenTTLKeeper.run` (the goroutine: the ticker, the shared `simpleTokensMu`), `.stop`,
    `.addSimpleToken`, `.resetSimpleToken`, `.deleteSimpleToken`.
  - `tokenNop.{enable, disable, invalidateUser, genTokenPrefix, info, assign}`: trivial, one line
    each, or one law `tokenNop_isProvider` proved from them.
  - `permSlice.{Len, Less, Swap}`: the instance of Perennial's sorter contract that
    `RoleGrantPermission`'s `sort.Sort` needs (old: `auth.permSlice_isSorter`).
  - `tokenJWT.*`: names only, so a trust boundary. One assumed bundle instance
    (`newTokenProviderJWT.spec`'s post) is acceptable.
- **S7. The bundle's contract is prose only.** `tokenProviderAt`/`tpOpen` have no laws
  (`Api.lean`'s docstring; `Internal.lean`: only `tpOpen_persistent`). `authInfoFromToken.spec`,
  `Authenticate.spec`, `WithRoot.spec` and `GenTokenPrefix.spec` call the interface's methods with
  nothing to apply. Add the method triples as laws over `tpOpen`: `info` gives `tokenUser`, `assign`
  from `authnCtx` or index 0, `enable`/`disable` with the keeper's `threadTok`, and so on. Add one
  instance law per concrete provider.
- **S8. Nonissue precision.**
  - `etcd-auth-revision-before-visible.md`: only **linearizable** reads block. Serializable reads
    are unconstrained by W0, and watches need only a reached state. State that W0's
    `permittedSince` generalization would make it `blocks-proof: no`.
  - `etcd-auth-password-72-byte-prefix.md`: bcrypt hashes `pw ++ [0]` (`bcrypt.go`,
    `expensiveBlowfishSetup`), so a **71-byte** password also accepts `pw ++ "\x00" ++ s`. NUL is
    valid UTF-8 in a proto3 string.
  - `etcd-auth-withroot-token-collision-panic.md`: the health checks (`health.go:222,434`) issue
    root tokens too.
- **S9. Users lists.** `WithRoot`: add `etcdhttp/health.go:222,434` (2c's `Range` already names
  them). `IsAuthEnabled`: add `embed/serve.go:465` (the gateway's certificate guard; no fact used
  beyond "a recorded state's flag").
- **S10. Missing message laws (3h's, provisional).** Nothing derives `authnRespAt p tok ⊢ ⌜p ≠ null⌝`.
  `ReqAuthenticateApply`'s `resp == nil` panic needs it, and 3a's `resp.Header = a.newHeader()`
  (`apply/backend.go:160-162`) needs a `Header` field law of `authRespAt`/`authnRespAt`. Request
  them of 3h.
- **S11. `Authenticate.spec`'s error is too weak for 3a.** The post says `err ≠ nil` with auth on.
  3a asked for `ErrAuthFailed` for an absent or password-less user (`store.go:322-330`; "from 3a"
  item 3), and W0's `authenticate` answers `.authFailed`. Split it: absent or password-less gives
  `errOf .authFailed`; otherwise the provider's error (no-op: `errOf .authFailed`; JWT: any).
- **S12. `ctxCertUser`'s docstring** should require the incoming metadata to be present:
  `AuthInfoFromTLS` returns nil when `metadata.FromIncomingContext` fails (`store.go:1038-1041`).
  It is 2a's realization, but the definition is 3d's text.
- **S13. `Recover` with a snapshot whose auth is off does not disable the provider** (the author's
  margin). If the member skipped an `AuthDisable` through the snapshot, the tokens issued before it
  stay valid on this member after a later `AuthEnable`; the members that applied it dropped them.
  It does not break `tokenUser` (same user), so it is not a proof issue, but it is a behavior worth a
  nonissue file.
- **S14. Following W0's working tree.** Its credential model (`UserRec.password` is the stored hash;
  `pwHash`/`pwMatch`) makes 3d's `hashedPw`, `CheckPassword.spec`'s `p ≠ pw` arm and the header's
  "the model keeps a user's password" out of date. Restate `CheckPassword`'s `authFailed` arm as
  `¬ pwMatch c pw`. `ReqTokenUser`/`ReqWithRoot` become provable once `tokenUser_agree` is committed.

## Snippets (provability)

| snippet | verdict |
|---|---|
| `ReqCheckPass`, `ReqNoUser`, `ReqAdminCheck`, `ReqEnabledFlag`, `ReqNoToken`, `ReqCertUser`, `ReqBoot`, `ReqCloseAfterStop` | provable as sketched |
| `ReqWriterCheck` | provable only through its `ErrAuthOldRevision` escape (F6) |
| `ReqAdminSteps`, `ReqRevisionBumped`, `ReqUserAddThenCheck` | currently provable only vacuously (F1). After the F1 fix, `ReqAdminSteps`'s `RoleGrantPermission` panic is unprovable while W0 allows `invalidAuthMgmt` at any state (F2, S4), at `HEAD` and in the working tree |
| `ReqRecover` | needs W0's revision monotonicity along `AuthReach` (true of the model) and S2's `a'.rev < 2^64` |
| `ReqTokenUser`, `ReqWithRoot` | need W0's `tokenUser_agree` (working tree); `ReqWithRoot` also needs `rootTokOk` (F5) |
| `ReqAuthenticateApply` | needs S10's non-null law |

Uncovered patterns: none of substance. The health checks' `WithRoot` is the same pattern as the
lessor's.

## Targets ranked by need of revision

1. `Api.lean`: `admStep`/`admNext`/`AdminTriple` (F1, F2), `checkPost` (F6), `authReqAt` (S3, S4),
   the provider bundle's laws (S7).
2. The admin specs (all through `AdminTriple`), `AuthEnable`, `AuthDisable`, `Recover` (F1, F2, S2);
   `RoleGet` (F3, stale once W0 commits).
3. `WithRoot` (F5: a decision); `Authenticate` (S11).
4. The token providers' and `permSlice`'s missing specs (S6).
5. The readers (`IsRangePermitted`/…, `Revision`, `AuthInfoFromCtx`/`TLS`): sound; S1's ordering is
   a 2d/3d boundary question.
6. The bcrypt boundary and the constructors: sound; nonissue wording only (S8).

## Verdict

Not done: a round 2 is needed.
- F1 is a soundness defect that makes every changing admin spec and `Recover`'s premise false or
  vacuous; it is mechanical to fix.
- F2 needs the store's step stated as the function the code computes.
- F4 and F5 are decisions for the user. F4: W0's `permittedSince` generalization, or the fork fix.
  F5: the fork fix to `assignSimpleTokenToUser`.
- F6 is a one-line strengthening.

The four-view timing, the reader specs and the bcrypt boundary are sound and well argued.
