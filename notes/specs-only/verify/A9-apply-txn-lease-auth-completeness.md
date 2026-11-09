# A9 (apply, txn, lease, auth, bcrypt): completeness verification (2026-11-09, HEAD `1aa6fc1337`)

Reviewer: independent, completeness kind. Read-only except this file. Findings were formed before
reading `open-questions.md`, `integration-*.md`, `batch-*.md` and `req/`; afterwards each was checked
against them (status noted per finding).

## Verdicts

| batch | verdict | first-tier |
|---|---|---|
| 3a apply (`etcdserver/apply/`) | **FAIL** | F6 (and the users of `CheckTxnAuth` through F1) |
| 3b txn (`etcdserver/txn/`) | **PASS** | none (its mvcc premises come through 3a's provisional `kvOk`/`kvSt`, which are 3a's/2d's) |
| 3c lease (`lease/`, incl. 2e's `lease/leasehttp/`) | **FAIL** | F2, F3, F9 |
| 3d auth (`auth/`) + bcrypt (`golang_org/x/crypto/bcrypt/`) | **FAIL** (one recorded open decision as well: `rootTokOk`, open-questions F2) | F1, F4, F5, F7, F8 |

Counts: **241 spec files** in the area (apply 72, txn 47, lease 43 + leasehttp 1, auth 75, bcrypt 2)
checked for coverage; **56 snippets** (`examples/specreq/{apply,txn,lease,auth}`) checked against the
user patterns; **35 user patterns** (about 70 call sites in the pinned etcd sources and
`examples/mvccrand`): **19 close**, **15 do not**, **1 waits on a recorded user decision**. Caller
specs checked: `EtcdServer.{Range, Txn, checkLeaseRenew, checkLeaseTimeToLive, checkLeaseLeases,
LeaseRenew, AuthInfoFromCtx, Authenticate, UserAdd, applyEntryNormal, applySnapshot}`, `NewServer`,
`serverWatchStream.isWatchPermitted`, mvcc's `putLs`/`delLs`/`RestoreLs`, `mvccDeleter_rdOk`,
`NewStore`, 2d's `srvReadAt_lessor`/`srvReader_lessor`/`srvReadAt_auth`.

**Coverage** (old tree `specs-ref`): every spec file of the five packages exists here, and every
`def X.spec` of each old file is defined in the new file of the same name. Complete.

## What is good

- **Lease (3c).** The writer/reader split (`lessorState` exclusive, `lessorAt`/`lessorLb` history
  with one reader spec serving the writer through `lessorState_le`/`lessorAt_agree`) fits all three
  user groups: mvcc's put/delete/restore (`putLs`, `delLs`, `RestoreLs` are exactly the
  `GetLease`/`Detach`/`Attach` steps, `kvstore_txn.go:223-290`, `335-345`), the request path's
  `Lookup`/`Keys`/`Leases`/`Remaining`/`TTL`/`Demoted` (`v3_server.go:512,592,624,645-670,738,773`,
  with 2d's `srvReadAt_lessor`/`srvReader_lessor`), and the lifecycle (`Promote`, `Demote`, `Stop`,
  `ExpiredLeasesC` with `expiredCh_recv`, `Recover`). `rdOk` lets mvcc prove the deleter once
  (`mvccDeleter_rdOk`) and the applier compose. The backend predicates all have 4a's introduction
  laws (`Backend.leaseBeOk_intro`, `leaseBeLeases_intro`, `leaseBeHook_intro`, `leaseHookRun_intro`,
  `leaseTxHeld_intro`, `LeaseBackend.lean:79-107`).
- **Txn (3b).** Every request-path use closes: `Range` (`v3_server.go:149,199,223`) over the `□ AU`
  that 2d's `srvReadAt_mvcc` gives, `Count` (`:255`), `IsTxnReadonly`/`IsTxnSerializable`
  (`:326,345`), read-only `Txn` (`:366`, `txnSafe` from 2c's `txnChecked_safe`), the warnings
  (`:126,359`), `IsDefaultOrdering`/`HasRevisionFilters` (`api/v3rpc/key.go:173,176`). Snippets cover
  each pattern.
- **Auth (3d).** The three-view reader contract (`checkPost`) is exactly what the code guarantees, and
  a **pass** gives what the watch server needs (`isWatchPermitted`: each `checkOk` disjunct is one
  state's `permits`, `authAt_reached` makes it reached). The writer's exact check (`authCur_at`,
  `authAt_le`) serves the auth applier. `CheckPassword` reads the revision from the same read
  transaction as the user (`store.go`'s closure), and the spec says so (`uint.nat r = ax.rev`).
- **Apply (3a).** `Apply.spec`/`isUber_apply` fit `applyEntryNormal` (`server.go:1995`), including the
  replay (`v3 = false`) and the admin refusal that returns a non-nil result even in the replay
  (`auth.go:52-58`, the `needAdmin` side condition of `ar = null`).

## First-tier findings

### F1. A read's permission **denial** is not at one auth state; the read path's callers need one (users: 2c `Range`, `RangeStream`, read-only `Txn`; 3d `IsRangePermitted`, 3a `CheckTxnAuth`)

- **Principle:** complete (the post gives what the caller needs) / sound caller model.
- **Evidence.** `authStore.isOpPermitted` (`auth/store.go:862-901`) reads the flag
  (`IsAuthEnabled`, under `enabledMu.RLock`, released), then the revision atomic, then the user
  under `lockedReadTx`, then the permission cache. `checkPost`'s denial is `checkDenied u rev t rng af
  ax ac` over three different recorded states (`auth/Api.lean:280-284`); 3d's header says so. 2c's
  `EtcdServer.Range` sketch fires the denial "at `histAt γ kp`, `Step`'s `permErr`"
  (`EtcdServer__Range.lean:23-27`), and W0's `kvStep .range` (and `.txn` read-only) admits a
  denial only by `¬ σ.permits`, `σ.invertedDeny` or `σ.deniedSince lo who ps`, each **one** auth
  state (`api/v3/Model.lean:888-890, 960-963, 1000-1003`); `permissionDenied` is not a refusal
  (`EtcdErr.refusal`, `Model.lean:373`), so the server cannot give the update back either.
  Execution: user `u` (not root) covered for `k`, auth on, at state 0. A reader reads the flag
  (on) and the revision (unchanged, so no `ErrAuthOldRevision`); the apply thread then applies
  `AuthDisable` (state 1: off) and `RoleRevokePermission` of `u`'s role (state 2: off, not covered;
  `refreshRangePermCache` and the batch's `Unlock` publish it); the reader reads the user (not root)
  and the cache (not covered): `ErrPermissionDenied`. At states 0, 1 and 2 the read is permitted
  (covered, or auth off), so no single auth state since `lo` denies it.
- **Callers affected:** `EtcdServer.Range`/`RangeStream`/`Txn` (read-only) proofs of the denial
  branch; snippets: none covers a denial on the read path (`auth/check.go`'s `ReqCheckPass` covers
  passes only).
- **Fix.** The 3d spec is right (the code does not give one state). Weaken W0's read denial to the
  three views it gets: `deniedSince lo who ps := ∃ jf jx jc ≥ lo, enabled at jf ∧ ¬ root at jx ∧
  (¬ covers at jc ∨ inverted)` (the `checkDenied` shape over `authTables`), and have 2c fire it from
  `checkPost` through `srvReadAt_auth`. Add a snippet of a denied read. This is also a (benign) etcd
  anomaly, a permission error for a read permitted at every point of the call: by the repository's
  rules it should be recorded in `nonissues/` (code reading, no test; a test could promote it with a
  sleep between `Revision()` and `lockedReadTx` in `isOpPermitted`). Not recorded anywhere
  (`open-questions.md` F1 is about passes; `batch-3d.md:50-51` notes the shape but nobody carried it
  to W0/2c).

### F2. The checkpointer's contract `ckptOk` cannot be met by the server's closure (3c `ckptOk`, `lessor.SetCheckpointer`, `lessor.Renew`; user 2e `NewServer`)

- **Principle:** every premise has a source the caller sees; a clause is stated over what its user
  holds.
- **Evidence.** `ckptOk cp R` (`lease/Api.lean:375-382`): `{{ R ∗ Context.ctxOk ctx ∗ msgAt … }} cp ctx
  lc {{ nil ∨ ErrNotPrimary }}` for **every** `ctx` with `ctxOk`, and no thread token. The server's
  closure (`server.go:395-403`) calls `srv.raftRequest(ctx, …)`, whose spec takes `threadTok`,
  `reqCtxOk ctx`, `reqPrin ctx p tls` (`EtcdServer__raftRequest.lean:50`). `R := srvStarted` is
  persistent and cannot yield a `threadTok`; an arbitrary `ctxOk` context gives neither `reqCtxOk`
  nor `reqPrin` (they are introduced only for `Background()`-derived contexts, `ApiReq.lean:288-291`).
  The lessor always passes `context.Background()` (`lessor.go:437,679`). `Renew` (which calls the
  checkpointer, `lessor.go:437`) takes no thread token (`lessor__Renew.lean`), though its caller
  `LeaseRenew` holds one. The snippet `ReqPromoteCheckpointer` uses a closure that calls nothing,
  so it did not catch this.
- **Fix.** `ckptOk` at `ctx = GoInterface.ok context.backgroundCtxVal`, with `threadTok` in its pre and
  post; `Renew.spec` takes and returns the caller's `threadTok` and passes it to the checkpointer (the
  run loop lends its own). Make the snippet's checkpointer call something needing a thread token.
  Not recorded (open-questions 3.10 confirms the error restriction only).

### F3. `clusterOk` has no introduction: no caller can call `NewLessor` (3c `NewLessor`; users `NewServer` `server.go:344`, `examples/mvccrand/mvccrand.go:810`, snippet `ReqNewLessor`)

- **Principle:** every premise has a source the caller sees.
- **Evidence.** `clusterOk cl` is opaque (`lease/Api.lean:346-351`) with no law producing it; 2e's
  `membership/` has no `RaftCluster.Version` spec and no `isCluster ⊢ Lease.clusterOk` law (only
  `Api.lean`, `RaftCluster__SetVersionChangedNotifier.lean`). `NewLessor.spec` takes `clusterOk cl`.
  Even a client with its own `Version()` (mvccrand's `noCluster{}`, the snippet's) cannot establish an
  opaque predicate, so `ReqNewLessor`'s "clusterOk of noCluster" has no law to cite.
- **Fix.** Make `clusterOk` transparent: the `Version` method's triple through the interface (`□ WP
  (cl.Version()) {{ v, v = nil ∨ readable *semver.Version }}`, a bundle as `sync.isLocker`), so any
  client proves it for its type; 2e proves it for `*RaftCluster`. Known since I5 (`integration-I5.md:
  496,523,568`, `req/..._membership.md` item 1), unresolved; not a user decision.

### F4. Three of 3d's resources have no introduction (3d `authBackendAt`, `authHook`, `authnCtx`; users `NewServer` `server.go:369`, `applySnapshot` `server.go:1127`, 3a's ten admin appliers and `applierV3backend.Authenticate`)

- **Principle:** every premise has a source the caller sees; laws for what clients would unfold.
- **Evidence.** `authBackendAt be a` (`auth/Api.lean:378`), `authHook γa Pre Q` (`:419`) and
  `authnCtx γa ctx name idx` (`:330`) are opaque, and no law anywhere concludes them (searched all of
  `Spec/`). `NewAuthStore.spec` and `authStore.Recover.spec` take `authBackendAt`; the caller holds
  only 4b's `NewAuthBackend` post (`abe ↦□ authBackend.mk be lg`, `schema/NewAuthBackend.lean`) and
  4a's backend parts. Every admin method (`AdminTriple`) takes `authHook`; 3a's sketches say "from
  `R`" (`applierV3backend__UserAdd.lean:10`), but nothing turns the server's hook into it (the lessor
  has `Backend.leaseHookRun_intro`; auth has no analogue). `authStore.Authenticate.spec` takes
  `authnCtx`; 3a's sketch says `context.WithValue` twice "gives" it
  (`applierV3backend__Authenticate.lean:7`), but no law does. Snippets `ReqBoot`, `ReqRecover`,
  `ReqAuthenticateApply` assume them.
- **Fix.** Laws in 3d (or 4a, as for the lessor): `authBackendAt_intro` from `NewAuthBackend`'s post
  and 4a's parts of the three auth buckets at `a` (the realization the docstring already states);
  `authHook_intro` from 4a's `∀ q, Backend.hookRun γb q Pk f Pre Q` at the store's backend (as
  `leaseHookRun_intro`); `authnCtx_intro` from `Context.ctxValueAt` of the two keys with the index and
  prefix values and `tokenUser γ (p ++ "." ++ decimal idx) name`. Known in I5 (`integration-I5.md:
  139,309`) and open-questions 4.7 (design confirmation only); unresolved.

### F5. 3d's context predicates are not grpc's, so no caller can call `AuthInfoFromCtx`/`AuthInfoFromTLS` (users: `EtcdServer.AuthInfoFromCtx` `v3_server.go:1207,1214`, hence every request's principal; `WithRoot`)

- **Principle:** every premise has a source the caller sees.
- **Evidence.** `Auth.ctxInMD`, `Auth.ctxPeerCN`, `Auth.ctxCertUser` are opaque in `auth/Api.lean`
  (`:389, :398, :409`); `ctxToken` (in `AuthInfoFromCtx.spec`'s pre) is over `Auth.ctxInMD`, and
  `AuthInfoFromTLS.spec` takes `Auth.ctxCertUser`. The introduction laws exist only for `Grpc.ctxInMD`,
  `Grpc.ctxPeerCN` and the transparent `Grpc.ctxCertUser` (`grpc/Api.lean:422-436, 871-886`; 2c's
  `ctxNoIncoming` is over `Grpc.*`, `ApiReq.lean:281`; v3rpc's `ctxNoIncoming_inMD`). grpc's file
  says "the owner of `server/v3/auth/Api.lean` should define them as these" (`grpc/Api.lean:416`).
- **Fix.** Replace the three opaques by `abbrev`s of `Grpc.ctxInMD`, `Grpc.ctxPeerCN`,
  `Grpc.ctxCertUser` (and drop the duplicate `MD`). Known (`integration-X.md:180`), unresolved.

### F6. The uber-applier's constructor carries no source for the lessor's and the auth store's hook contracts or the range deleter's contract (3a `optsOk`/`optsSt` → `beAt`/`stAt`; specs `applierV3backend.{LeaseGrant, LeaseCheckpoint, LeaseRevoke}` and the ten admin methods; user `NewServer`/`applySnapshot` via `NewUberApplier`)

- **Principle:** every premise has a source; a clause is stated over what its user holds.
- **Evidence.** `newApplierV3Backend`'s sketch: `beAt` and `stAt` are exactly `optsOk`, `optsSt`
  (`newApplierV3Backend.lean:6`). `optsOk` (`apply/Api.lean:735-740`) holds `lessorOk` (only
  `Lease.isLessor`) and `authOk` (only `Auth.authStoreAt`); `optsSt` holds `lessorSt` (only
  `isLessor ∗ lessorState`, with `ls.rd` unconstrained) and `authSt`. But `lessor.Grant.spec` and
  `lessor.Checkpoint.spec` take `Lease.beHook ls.be Pk f ∗ Lease.beHookRun ls.be Pk f Pre Q`;
  `lessor.Revoke.spec` takes `⌜ls.rd ≠ func.nil⌝ ∗ Lease.rdOk γl ls.rd n ls P D Q`; every
  `Auth.AdminTriple` takes `Auth.authHook`. The backend appliers' sketches source them "from `R`"
  (`applierV3backend__LeaseGrant.lean:8-12`) or "inside `stAt`" (`lessorSt`'s docstring,
  `Api.lean:664`), but `R` is an arbitrary parameter the apply proof cannot open, and nothing puts
  them in `stAt`. Only mvcc's hook has a slot (`kvOk`, provisional).
- **Fix.** Add to `optsOk` persistent rows: `Lease.beHook` of the lessor's backend and a `□`-producer
  of `Lease.beHookRun be Pk f R' Q` (under the lent `R`), and an `Auth.authHook` producer (after F4);
  add to `lessorSt` the deleter's facts (`ls.rd ≠ func.nil` and `mvccDeleter ls.rd γm` with the
  `kbHeld`/`beTxHeld` identification, from which `Mvcc.mvccDeleter_rdOk` gives `rdOk` at each call).
  Known in I5 as requests to 2d (`integration-I5.md:118,283-285`); unresolved.

### F7. `NewTokenProvider`'s `waiterOk` is false of the server's waiter when `NewServer` calls it (3d `NewTokenProvider`; user `NewServer` `server.go:351-354`)

- **Principle:** sound/complete: a premise the caller can establish with the value it passes.
- **Evidence.** `waiterOk iw` (`auth/Api.lean:545-548`) is `□ ∀ i, WP iw i {{ recvOk }}` from the call
  on. The server passes `func(index uint64) <-chan struct{} { return srv.applyWait.Wait(index) }`, and
  `srv.applyWait` is assigned only in `start()` (`server.go:568`); before it, the call is a method
  call on a nil interface (a panic). The simple provider calls the waiter in `info`
  (`simple_token.go:240`), reached only through `AuthInfoFromCtx` after the server starts, so etcd
  is fine, but `NewServer` cannot prove the premise. 2d asked for this (`req/..._auth.md`, "from 2d
  (round 1)", item 2); the snippet `ReqBoot` takes a waiter that works from the start.
- **Fix.** Gate the waiter like the checkpointer: `waiterOk iw R` (calls need `□ R`), with the
  provider's `info` taking `□ R` from `AuthInfoFromCtx`'s caller (`R := srvStarted`, which every
  request-path spec holds), or give `NewTokenProvider` a gate token as `SetCheckpointer` does.

### F8. bcrypt's error is unconstrained; the server returns it and owes its shape (bcrypt `GenerateFromPassword`; users `EtcdServer.UserAdd`/`UserChangePassword`, `v3_server.go:893,918`)

- **Principle:** the postcondition says what the caller inspects.
- **Evidence.** `GenerateFromPassword.spec`'s error disjunct is `err ≠ nil ∧ (72 < |pw| ∨ 31 < cost)`.
  With the store's cost in `[4, 31]` (`BcryptCost.spec`) the error is reachable by any client with a
  password over 72 bytes; `UserAdd` returns it as is (outcome 2, `EtcdServer__UserAdd.lean:8`), and
  every returned error must carry `srvErrShape` (not a context error, `Grpc.cmpErr`, a message,
  unmapped: `errors/Api.lean:137-141`), which nothing about `err` gives. The snippet
  `ReqUserAddThenCheck` assumes a short password.
- **Fix.** Name the value: for `72 < |pw|`, `err` is the package variable `bcrypt.ErrPasswordTooLong`
  (an `errors.New` value: comparable, its `Error()` message known), with its shape facts as a law of
  the boundary; add a snippet of a long password's refusal.

### F9. `RenewHTTP` says nothing of its error; the follower's `LeaseRenew` returns it on `errors.Is(err, ErrLeaseNotFound)` (2e's `lease/leasehttp/RenewHTTP`; user `EtcdServer.LeaseRenew` `v3_server.go:551-555`)

- **Principle:** the postcondition says what the caller inspects.
- **Evidence.** `RenewHTTP.spec`'s post is `threadTok` only. `LeaseRenew` calls `errors.Is(err,
  lease.ErrLeaseNotFound)` on it (an arbitrary error: `*url.Error` from `cc.Do`, `fmt.Errorf("%w")`)
  and returns it, owing `srvErrOf err .leaseNotFound ∗ srvErrShape err`. Its sketch claims "a TTL,
  `ErrLeaseNotFound`, other errors retried" (`EtcdServer__LeaseRenew.lean:14`), which the spec does
  not state. The Go code returns exactly `lease.ErrLeaseNotFound` on a 404 (`http.go:205-206`).
- **Fix.** Post: `err = nil`, or `errIs ErrLeaseNotFound err`, or an error on which `errors.Is` is safe
  and false for `ErrLeaseNotFound` (the `Grpc.cmpErr`/unwrap facts `errors.Is` needs). No lease snippet
  covers the forwarding path; add one (2c's `ReqKeepAlive` on a follower).

## Recorded open decision

- **`WithRoot`'s `rootTokOk`** (open-questions F2): with the default simple provider no caller has
  it, so `revokeExpiredLeases` (`server.go:881`) and the health checks (`health.go:222,434`) have no
  usable `WithRoot` spec with auth on. Pending the user's choice (fork fix or a premise).

## Second-tier / uncertain

- **`AuthReach a a'` for `Recover`** (`authStore__Recover.lean:51`): the sketch says 2d has it "from
  the cluster's history", but no law turns W0's `Reach` (or 3a's `applyStep_reach`) into
  `AuthReach σ.auth σ'.auth`. `AuthReach`'s `admStep` quantifies over all permitted callers, so it is
  plausible; a law in 3d or W0 would close it. Uncertain.
- **`authLb` for readers outside the read slot** (the watch server's `isWatchPermitted`, v3rpc's
  `isPermitted`): `IsRangePermitted`/`IsAdminPermitted` take `authLb γa i0`, and the only source is
  2d's `srvReadAt_auth` (through `srvApplied_zero`, `srvApplied_read`). A law `authStoreAt st γ γa ⊢
  authLb γa 0` would let any holder of the store call them; whether 2b's realization reaches
  `srvReadAt` I could not verify.
- **`authReqAt`, `reqMsgAt`, `irrMsgAt`** stay provisional (3h's): the admin methods' message premise
  has no producer yet (recorded in I5).
- **Cross-area coverage, affecting this area's users** (the server's batch, not this area): the old
  tree's `EtcdServer.AuthStore`, `EtcdServer.NewUberApplier`, `ensureLeadership`,
  `getTxPostLockInsideApplyHook`, `checkMembershipOperationPermission` (and others) have no file in the
  new `etcdserver/`; the watch server's `ag.AuthStore()` and the checkpointer closure's
  `ensureLeadership` go through them. For the A7/A8 reviewers to confirm.

## User patterns (35)

Lease: mvcc put/delete/restore (`kvstore_txn.go:233-345`, `kvstore.go:398`) closes; mvcc
`SetRangeDeleter` (`kvstore.go:117`, `watchable_store.go:107`) closes; apply grant/checkpoint
(`backend.go:84,101`) **F6**; apply revoke (`backend.go:95`) **F6**; writer `Lookup` (`txn/put.go:83`,
`apply/auth.go:199`) closes; request-path reads (`v3_server.go:512-779`) close; `Renew`
(`v3_server.go:528`) **F2**; `NewLessor` (`server.go:344`) **F3**; `SetCheckpointer` (`server.go:395`)
**F2**; `Promote`/`Demote`/`Stop`/`ExpiredLeasesC`/`revokeExpiredLeases` (`server.go:1990,769,947,
835,855`) close; `Recover` (`server.go:1087`) closes; `RenewHTTP` (`v3_server.go:551`) **F9**;
mvccrand (`mvccrand.go:503-548,798,810`) **F3**.
Auth: read-path checks (`v3_server.go:146,183,575-779`, `CheckTxnAuth` `:355`) pass closes, denial
**F1**; watch create (`watch.go:248`) closes; `AuthInfoFromCtx`/`AuthInfoFromTLS` (`:1207,1214`)
**F5**; `IsAdminPermitted`/`IsAuthEnabled` (`server.go:1403`, `v3rpc/auth.go:188,192`,
`v3_server.go:1278`) close; `Authenticate`'s `CheckPassword`/`GenTokenPrefix`/`Revision`
(`:853-881`) close; `UserAdd`/`UserChangePassword` with bcrypt (`:893,918`) **F8**; `WithRoot`
(`server.go:881`, `health.go`) open decision; `Close` (`server.go:953`) closes; `Recover`
(`server.go:1127`) **F4**; `NewTokenProvider`/`NewAuthStore` (`server.go:351,369`) **F7, F4**; apply's
admin writes (`backend.go:139-263`) **F4, F6**; apply's `Authenticate` (`backend.go:157`) **F4**;
apply's writer checks (`apply/auth.go`) close.
Txn: `Range`, `Count`, readonly predicates, read-only `Txn`, warnings, `key.go` helpers, the apply's
`Put`/`DeleteRange`/`Txn`/`Range` (7 patterns) close.
Apply: `apply.Apply` from `applyEntryNormal` (`server.go:1995`) closes at the interface; the
constructor `NewUberApplier` (`server.go:1181-1197`) **F6**.
bcrypt: `CompareHashAndPassword` (3d's `CheckPassword`) closes; `GenerateFromPassword` **F8**.
