# Repair: group `apply-txn` (3a `etcdserver/apply`, 3b `etcdserver/txn`), 2026-11-09

From the 3a/3b parts of `A9-apply-txn-lease-auth-{provability,completeness}.md`. Files changed:
`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/{Api,ApiResult,NewUberApplier,newApplierV3Backend,
authApplierV3__Apply,applierV3backend__{Txn,Put,LeaseGrant,LeaseCheckpoint,LeaseRevoke,UserAdd,
UserDelete,UserChangePassword,UserGrantRole,UserRevokeRole,RoleAdd,RoleDelete,RoleGrantPermission,
RoleRevokePermission,AuthEnable,AuthDisable}}.lean`; `examples/specreq/apply/{apply,alarm}.go`.
No 3b file needed a change.

## Findings

### Provability (A9-…-provability.md)

- **F1 (Txn's `txnSafe`)**: fixed as suggested. `txnAdmitted t` (`apply/Api.lean`) is now
  `t.valid ∧ Txn.txnSafe t ∧ putOnce…`, so `op.ok` gives `txn.Txn.spec`'s `⌜txnSafe t⌝`;
  `apply/Api.lean` imports `txn/Api.lean` for it (no cycle: txn imports no apply module). The
  server supplies it from 2a's `txnChecked` through 2c's `txnChecked_safe`; the reviewer's related
  gap (no law gives `txnAdmitted` from `txnChecked`) is a request to server-core below.
- **F2 (`leasesLive`, `ls.rd ≠ nil`, `rdOk`)**: fixed. `lessorSt` now takes the KV and the
  backend (`lessorSt le kv be lt s`) and states `Txn.leasesLive s ls` (3b's own predicate, exactly
  what `txn.Put`/`txn.Txn` take), `ls.be = be`, `ls.rd ≠ func.nil`, and `kvDelOk kv γl be ls.rd`.
  `optsSt` instantiates it with `o.KV'`, `o.Backend'`. Fixed differently from the suggestion
  (`□ ∀ n ls P…, rdOk …` in `optsSt`): `rdOk`'s `P`/`D`/`Q` are the store's writer resources, which
  live in the provisional `kvSt`/`kvOk`, so the deleter's contract is a provisional slot of the same
  kind, `kvDelOk` (persistent, opaque), whose intended realization is 3e's
  `Mvcc.mvccDeleter_rdOk` premises (`mvccDeleter rd γ`, `mvccLessorIs γ γl`, the `kbHeld`/`beTxHeld`
  identification) at `kvOk`'s store; `mvccDeleter_rdOk` then gives `rdOk` per revocation. Its
  introduction goes with `kvOk`'s (request below). `kvDelOk` is in `persistent.spec`.
- **F3 (hook contracts)**: fixed. New transparent `hooksOk be R` in `optsOk` (so in `beAt`):
  the lessor's `Lease.beHook be Pk f ∗ □ Lease.beHookRun be Pk f R Q ∗ □ (Q ={⊤}=∗ Pk ∗ R)` at the
  options' backend (tied to the lessor's `ls.be` by `lessorSt`), and for the auth store, following
  lease-auth's repair (`repair-lease-auth.md`, "Requests to apply-txn"), a `□` producer of 3d's
  `Auth.authBeHook abe R Q` (with `□ (Q ={⊤}=∗ R)`) for every `*authBackend` `abe ↦□
  authBackend.mk be lg` wrapping the options' backend; `authSt` now takes the backend and holds
  3d's `Auth.authBeCur γa abe` at such a wrapper (4b's `NewAuthBackend` post), so 3d's
  `authHook_intro` gives each admin method's `Auth.authHook`. The lessor half is introducible today
  (4a's `leaseBeHook_intro`/`leaseHookRun_intro`); the auth half waits on 4a's `authBeHook`
  introduction (lease-auth requested it of 4a).
- **F4 (`opStep_step` too weak)**: fixed as suggested. New `ownStep who rq σ σ' res := kvStep ∨
  leaseStep ∨ authStep ∨ clusterStep` (W0's `Step` minus the refusal disjunct, `lo = 0`);
  `opStep_step` concludes it. Checked against the backend: its errors are mvcc's (`compacted`,
  `futureRev`, a put's `check`), the lessor's (`leaseNotFound`, `leaseExist`, `leaseTTLTooLarge`)
  and the auth store's, each in its request's step; `irrStep_step` still concludes `Step` (the gates
  refuse). `ReqApplyWrite` now closes: auth off and no alarm make `layersErr` none, `ownStep` of a
  valid put with a live lease is `kvStep`'s success. Its `Specs:` line cites `opStep_step`.
- **F5 (`aiAt` realization)**: fixed. The stated mutex invariant is `aa.authInfo ↦ ("", 0)` (every
  path resets it, `auth.go:54-55,60-61`), so a header-less request runs at `("", 0) = (ir.user,
  ir.revW)`; header of `apply/Api.lean` and `authApplierV3__Apply.lean`'s sketch.
- **Second tier**:
  - `ReqCorrupt`'s `Assumes:` now says "a valid Range" (`reqAdmitted`).
  - dispatch's deferred warnings need `msgOpt ar.Resp`: added the internal law
    `replyAt_msgOpt.spec` (`ApiResult.lean`): a method's reply lends `Txn.msgOpt resp m` (its fresh
    response, or a typed `nil`). The reviewer looked for it in 2c's `irrReply`, which is not where
    it belongs (`irrReply` is "anything" for a `.noop`).
  - `LeaseCheckpoint`'s non-`nil` response with `noAns`: closes, 2c's `irrReply` accepts any reply
    for `.noop` (`ApiReq.lean:383-390`). No change.
  - The nested-txn recursion of the `check*` helpers waits on W0/3h's `endsDecoded`/`opsDecoded`
    split laws (recorded, `integration-I5.md`). Not fixed here (not 3a's vocabulary to define).
- **3b (PASS WITH OPEN GAPS)**: the three self-declared gaps (`ctxErr_not_errIs`, `errIs_agree` /
  `errIs_ne_nil` at `.keyNotFound`, `rrOwn`'s `kvFits`) are owed by mvcc and `etcdserver/errors`:
  requests below. No 3b statement changed.

### Completeness (A9-…-completeness.md)

- **F6 (`optsOk`/`optsSt` carry no hooks / deleter)**: fixed, by the F2 and F3 repairs (`hooksOk` in
  `optsOk`; `lessorSt`'s `leasesLive`, `ls.be`, `ls.rd`, `kvDelOk` in `optsSt`). `NewUberApplier`,
  `newApplierV3Backend` sketches and every affected backend method's `Changes:` line updated
  (`verify-round: …`; no triple's statement changed, only the slots they read).
- **F1 (a read's denial at three auth states; users include `CheckTxnAuth`)**: 3a's
  `CheckTxnAuth.spec` already reports 3d's `checkPost` (the three views), which is what the code
  does; the fix is W0's `deniedSince` and 2c's firing (requests to client-core and server-core,
  below). The benign anomaly is 3d's code (`isOpPermitted`), for lease-auth to file in `nonissues/`.

### Sentinel errors (brief item 3)

- `txn`: already in the global encoding (`errIs err e := globalAddr X ↦□ err`, mvcc's, lease's,
  `etcdserver/errors`' sentinels). Its `errIs_ne_nil`/`errIs_agree` need each owner's init law to
  give its globals non-`nil` and pairwise distinct (requests below). `txn` and `apply` declare no
  sentinel of their own (`grep errors.New` in both packages: none).
- `apply`: its errors are `etcdserver/errors`' (`ErrCorrupt`, `ErrNoSpace`) and the stores', all
  through server-core's `srvErrOf err e` (`chkExact`, `replyAt_result`). `srvErrOf` and `srvErrVal`
  are pure opaques there, which is the encoding the brief rules out (`srvErrVal e` a fixed constant);
  apply follows whatever server-core switches to (request below). Nothing to change in apply's own
  statements until then.

## Requests to server-core

0. `NewServer`/`applySnapshot` must also give `authSt`'s `authBeCur` at the auth backend wrapping
   `s.be` (from `NewAuthStore`'s/`Recover`'s post) and `hooksOk`'s auth half (from 4a's
   `authBeHook` introduction).

1. `Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiReq.lean`: a law `txnChecked_admitted.spec : ∀ t,
   txnChecked t → Apply.txnAdmitted t` (or `txnChecked t → t.valid ∧ ∀ … putOnce evs`, with
   `txnChecked_safe` for the `txnSafe` conjunct): the apply thread's `ir.op.ok` for a transaction
   (`isUber_apply`'s premise) has no source otherwise (A9 provability F1, "related").
2. 2d (owner of the apply thread's mvcc authority): realize and introduce 3a's provisional `kvOk`,
   `kvSt` and the new `kvDelOk kv γl be rd` together (intended realizations in `apply/Api.lean`),
   from `NewStore`'s post (`mvccDeleter rd γ`, set as the lessor's deleter) and 4a's
   `Backend.leaseTxHeld_intro`; `NewServer` and `applySnapshot` need it for `NewUberApplier`'s new
   `optsSt` (A9 F2/F6). If you prefer, give me the realization and I state `kvDelOk_intro` in 3a.
3. `NewServer`/`applySnapshot`: `NewUberApplier`'s premises grew (`hooksOk` in `optsOk`;
   `lessorSt`'s `leasesLive`, `ls.be = opts.Backend`, `ls.rd ≠ nil`, `kvDelOk` in `optsSt`); the
   lessor's `ls.be` is `s.be` (`server.go:344,1193`; after a snapshot, `Recover`'s `newbe`).
4. `etcdserver/errors/Api.lean` (sentinels): `srvErrVal e` is a fixed constant and `srvErrOf` a pure
   predicate, which the brief's item 3 rules out; an init law giving each `Err*` global's value
   existentially (non-`nil`, pairwise distinct, `srvErrOf` of it) is what 3a's `chkExact` /
   `replyAt_result` and 3b's `errIs_ne_nil`/`errIs_agree` at `.keyNotFound` need (the latter: the
   global `ErrKeyNotFound` holds a value distinct from mvcc's and lease's sentinels).
5. W0/2c's read denial at three auth states (A9 completeness F1): 2c's `Range`/`Txn` read paths
   fire `checkPost`'s denial; with client-core's `deniedSince` reshaped (below) nothing changes in
   3a's `CheckTxnAuth`.

## Requests to client-core

1. `Spec/go_etcd_io/etcd/api/v3/Model.lean`: A9 completeness F1, `State.deniedSince lo who ps` as
   the three views `checkDenied` reports (flag at `jf`, backend at `jx`, cache at `jc`, all ≥ `lo`).

## Requests to mvcc

1. 3b's `ctxErr_not_errIs`: `rangeResOwn`'s `.ctxErr` outcome should say the error is none of the
   sentinels (`req/..._storage_mvcc.md`, "from 3b", item 1; still open).
2. 3b's `rrOwn` `kvFits` (a record's lease an `int64`): item 2 there, still open.
3. The init law giving `ErrCompacted`/`ErrFutureRev`'s globals non-`nil` and distinct from the other
   packages' sentinels (3b's `errIs_agree`).

## lease-auth's requests to apply-txn (handled)

- Slots for `Auth.authBeCur` and an `authBeHook` producer: `authSt ast be a` holds `authBeCur γa
  abe` with `abe ↦□ authBackend.mk be lg`; `hooksOk`'s auth half produces `authBeHook` at any such
  wrapper under `R` (see F3).
- `authnCtx γa` in sketches: `applierV3backend__Authenticate.lean` and `authnIdx`'s docstring now
  cite the transparent `Auth.authnCtx γ ctx name idx` (two `ctxValIs` from `context.WithValue`
  over `Background()`, client-core's value law, and `authnIdx`'s `tokenUser γ (simpleTok p idx)
  name`).
- The lease hook slot: 3a uses `Lease.beHookRun` (not mvcc's old `hookRun`) already; the stale
  name in `ReqGrantHook` is in lease-auth's snippet.

## server-boot's request to apply-txn (handled)

- `clusterVerOk ver := ∃ sv, Semver.parse ver = some sv ∧ Membership.verFits sv` (transparent, was a
  provisional opaque). `optsOk` holds 2e's `Membership.clusterVerInv γc` (the invariant
  `ClusterVersionSet`'s `Version`/`SetVersion` and `DowngradeInfoSet`'s `SetDowngradeInfo` fire their
  updates in), `optsSt` holds `∃ v, Membership.beVer o.Cluster' v` beside `beView` (the version is
  outside the model). `applierV3backend__{ClusterVersionSet,DowngradeInfoSet}.lean` sketches cite
  2e's `RaftCluster.Version/SetVersion/SetDowngradeInfo.spec`. Server-core/server-boot: `NewServer`
  and `applySnapshot` now owe `clusterVerInv` and `beVer` to `NewUberApplier`.

## Requests to lease-auth

1. (none new for the hook: `authHook_intro` + `authBeCur`/`authBeHook` close it once 4a introduces
   `authBeHook`.)
2. `ErrLeaseNotFound`'s global in the sentinel encoding (3b's `errIs .leaseNotFound`), non-`nil`
   and distinct from mvcc's and `etcdserver/errors`'.
3. The read-denial anomaly of `isOpPermitted` (A9 completeness F1: a permission error for a read
   permitted at every auth state the call spans) is 3d's code: a `nonissues/` entry.

## New decisions

- **`ownStep`**: the backend's operation is now pinned to the request's own step (no refusal). This
  is what the code does and what a client needs to learn "a valid write was not refused"; it adds
  nothing to the trust base (a law the apply proof proves).
- **The deleter's contract as a provisional slot (`kvDelOk`) beside `kvOk`/`kvSt`**, not as an
  `rdOk` producer inside `optsSt`: `rdOk`'s resources are the store's writer resources, which only
  `kvSt`/`kvOk`'s realization names, so the three are introduced together by their owner.

## Build

`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/etcdserver/{apply,txn}`: OK (122 modules), after
the lease-auth and server-boot requests; the importers `etcdserver.ApiApply`, `ApiReq` also build.
`cd examples && go vet ./specreq/apply/... ./specreq/txn/...`: clean.

## Second pass (coordinator's `second-pass.md`)

- **ApiResult `srvErrOf` → `srvErr`** (server-core): `chkExact` is now `⌜err = nil ∧ checkErr … =
  none⌝ ∨ ∃ e, ⌜checkErr … = some e⌝ ∗ EtcdServer.srvErr err e`; `replyAt_result`'s error case
  `EtcdServer.srvErr err e ∗ srvErrShape err`. No `srvErrOf`/`srvErrVal` is left in `apply/` or
  `txn/` (the txn/Api comment cites `sentinelAt`, `errors_init`, `srvErr_fun`).
- **`txn/Api.lean` comment** (server-core): done, as above.
- **`authnIdx` conditional** (server-core): its meaning is now "under `R`, if the entry being
  applied (whose index `ConsistentIndex()` answers) asks `Authenticate(name, tok)`, the cluster
  issued `tok.idx` to `name`"; the unconditional reading was false for other names, and 2d's
  `applyLent_opts` gives it for every `name`, `tok`.
- **"Provisional" dropped** on `statusOk`, `snapSrvOk`, `ciOk`, `authnIdx` (introduced by 2d's
  `applyLent_opts`); `kvDelOk`'s docstring and the I5 header note cite 2d's `srvStores_kv` for `kvOk`,
  `kvSt`, `kvDelOk`.
- **`endsDecoded`/`opsDecoded`** (grpc-v3rpc's P-F2): now transparent, `endsDecoded rt :=
  EtcdServerPb.endsDecoded TxnRequest.ty rt` and `opsDecoded sl := EtcdServerPb.opsDecoded sl` (3h's
  share-holding forms); their `persistent.spec` conjuncts are dropped. `reqMsgAt_endsDecoded` now
  concludes `□ endsDecoded p` (the entry is read-only: 3h's `endsDecoded_of_canon`,
  `endsDecoded_ro`). **Differently from the suggestion** ("the persistent closure"): `CheckTxnAuth`
  is also called by the request path, which holds the request at a share, so a persistent
  `endsDecoded` could not be produced there; instead `CheckTxnAuth`, `checkTxnPermission` and
  `checkTxnReqsPermission` give `endsDecoded`/`opsDecoded` back in their posts, and the apply
  thread's callers use the `□` form. The nested recursion now cites 3h's `endsDecoded_txn`/`_op`.
- **`stringerOk` → `stringerAt`** (grpc-v3rpc's C-F6): txn's provisional persistent `stringerOk` and
  its persistence law are deleted; `WarnOfExpensiveRequest`, `WarnOfFailedRequest`,
  `WarnOfExpensiveReadOnlyRangeRequest`, `warnOfExpensiveGenericRequest` take
  `EtcdServerPb.stringerAt req` and give it back; `txn/Api.lean` imports 3h's `Stringer`. The
  dispatch sketch names the stringer of `&pb.InternalRaftStringer{Request: r}`.
- **`Proto.norm`-survival laws**: none owed. Neither package defines a model relation over
  `Proto.Content` (`xModels c m`): txn's reply predicates are over W0's `Wire.lean` (owned by
  client-core/3h), `msgOpt` is a resource over any content, and apply's `irrMsgAt`/`reqMsgAt` are
  3h's provisional opaques.

- **mvcc's two items met** (mvcc, via the coordinator): txn's `ctxErr` is now realized from 3e's
  `Mvcc.rangeCtxErr` (new law `ctxErr_of_range : Mvcc.rangeCtxErr err ⊢ ctxErr err`; or
  `executeTxn`'s `fmt.Errorf("applyTxn: failed Range: %w", …)` wrapping of one), so
  `ctxErr_ne_nil`/`ctxErr_not_errIs` follow from `rangeCtxErr_ne_nil`/`_fresh`; `rrOwn`'s `kvFits`
  from `kvsFit`'s `kvSortOk` (lease bounds included). `txn/Api.lean`'s "owed" note and
  `executeRange.lean`'s sketch updated (the old `context.isCtxErr` claim was false). Builds against
  `rangeResOwn`'s changed `.ctxErr` case; no statement changed.

- **`stringerAt_irr`** (grpc-v3rpc, last item): `uberApplier__dispatch.lean`'s sketch cites 3h's
  `EtcdServerPb.stringerAt_irr` for the warnings' `&pb.InternalRaftStringer{Request: r}`
  (`uber_applier.go:99,101`); new law `irrMsgAt_msg.spec` (`apply/Api.lean`): `irrMsgAt p ir ⊢ ∃ c,
  Proto.msgAt InternalRaftRequest.ty p DFrac.discard c`, the read-only message it needs. The request
  below is met. Build: `apply/` OK (74 modules).

### Requests to grpc-v3rpc (second pass)

1. A `stringerAt` introduction for `&pb.InternalRaftStringer{Request: r}` over a read-only
   `InternalRaftRequest` (the uber-applier's `dispatch` logs it: `uber_applier.go:99,101`), as
   `stringerAt_discard` does for a message.

### Build (second pass)

`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/etcdserver/{apply,txn}`: OK (122 modules);
importers `etcdserver.{ApiApply,ApiReq,EtcdServer__Range,EtcdServer__Txn}` OK; `go vet
./specreq/apply/... ./specreq/txn/...` clean.
