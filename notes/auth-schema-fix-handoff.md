# auth-schema-fix: handoff (2026-11-12, updated after F4)

Stage of etcd-grove-81: make the auth results non-vacuous (S1: remove `auth.ValidSpec`; S0's F1-F4
in `authSchemaSrv`). Worktree `/shared/etcd-grove-authfix`, branch `auth-schema-fix` (from lean
`2f8cf80b7e`). Plan: `/shared/tmp/auth-safe/fix-plan.md`; Freeze package (in progress):
`/shared/tmp/auth-safe/freeze-fix.md`. Not landed; STOP for 81's axiom re-review once the targeted
builds pass.

## Done (committed, targeted builds pass)

- F3 (`e450457d89`): `auth.roleListed n := n ≠ [] ∧ GoStringLt n [0xff]`; `rolesOut` and
  `roleListOut` (RoleList's reply) list only those roles. nonissues F3 and F4 written.
- F2 (`350380537e`): `authBkLend` hands an abstract observation `RL` with the law
  `□ ∀ r, RL -∗ backend.rbOwn d.γB r -∗ ⌜authBucketsAt st r⌝ ∗ RL ∗ backend.rbOwn d.γB r`
  (no `rbPart`: no write authority); `bkLendW` the same shape; `srvAuthApplyResB_lend`,
  `acRes_lend`, `bkLendW_none`, the window (SnapSendBranch: the law applied inside the
  snapshot's observation, then `snapObsA` at no lent bucket) adapted. Built: SnapSendBranch,
  StoreLatest, AuthComp, AuthSrv, SnapAuthRecover, ApplyAllSnap.
- Go evidence for F4's supply: `/shared/tmp/auth-safe/fix-tests/irr_utf8_test.go` (passes at the
  server pin: `pbutil.MustUnmarshalMessage` panics on an InternalRaftRequest whose UserGrantRole
  role/user, UserAdd name or RoleAdd name is not valid UTF-8).

## S1 (partly committed; STOPPED at blocker 2, reported to etcd-grove-81 2026-11-12)

Committed (targeted build passes: TokenKeeperRun, authStore__AuthInfoFromCtx/authInfoFromToken,
AuthReqDerive): the token contract's `info` clause takes the hlc-generic `auth.ctxDoneRecv ci`
(`auth/CtxDone.lean`, with `auth.anyRecv` moved there from TokenSimple, and the law
`auth.ctxDoneRecv_of_ctxDoneAny` at hasLC); `tokenSimple_isValid` over it (nil Done:
`chan.wp_select_blocking_nil` + `chan.nilClausePre_recv`); `ValidSpec`, `tokenSimple_info`,
`tokenProviderOkCtx`, `tokenSimple_okCtx` deleted; `tokenSimple_okA(_run)` take `simpleWaitOk p`;
the store specs `authInfoFromToken`/`AuthInfoFromCtx` take `ctxDoneRecv`; AuthReqDerive converts
isReqAuth's `ctxDoneAny`. Results' `token_simple_ok` now states `tokenProviderOkA`.

**Not building yet**: `etcdserver/AuthSrv.lean` (`authSrvTP_on` still takes `hValid :
auth.ValidSpec`) and its users in `etcdserver/Results.lean` (`srv_auth_tp_on`, `server_new_auth_on`)
and `examples/etcd/auth/Results.lean`. Blocker 2: 81's route (authSrvTP's pre carries the waiter
contract, NewServer discharges it) fails: the waiter closure reads `srv.applyWait`, which Go sets
only in `start` (server.go:568), so at NewServer the field is nil and the closure panics if called.
Waiting for 81's decision (questions.md).

## F4 done (commit 350baf65a5; targeted builds pass, see "Build status")

Form differs from the plan's "bundled with permKeysOk" (recorded in questions.md as a form decided
by the agent): `auth.rolesUtf8` (Model.lean) lives in the fuel's `authSmall` (field `utf8`,
Fuel.lean), which every `StepSmall` already preserves and the snapshot's `histWf` includes;
`stepOk` (Steps.lean) gives the found state's and a `next` state's `rolesUtf8`, so no store spec
gained a premise. Trusted: UnsafePutUser's `∀ x ∈ ur.roles, utf8Valid x` (authBatchTxLkR and
authBatchTxLk); NEW law `apply.irrDecode_utf8` (apply/InvRequest.lean: only the grant's role).
Supply path: `irrWrapperIs` carries `⌜irrUtf8 rq⌝` (Apply.lean/ApplyFnAdmin.lean discharge it
from `Hdec`), DispatchAdmin → `AdminReq.nameOk` (grant: `∧ utf8Valid ro`) → AdminChain →
`UserGrantRole.fuelSpec(X)` (new premise `utf8Valid role`) → `stepSmall_userGrantRole … hu8`;
SnapAuthRecover's `adminStateR_wf`/`adminNext_wf` take `irrUtf8 rq` (from `irrDecode_utf8`).
Statement changes (weaker; to report): Results' `apply_UserGrantRole_fuel` (+`utf8Valid role`),
`stepOk` stronger (the `apply_*_step` results). Freeze package F4 section written.

## Next, in order

1. **F1** (not started; the biggest step). Decided: `Wb` parameter on the write contracts
   (authBatchTxLkR/OkR, authWBackendOkR, and the store views authBatchTxLk/authBatchTxOk/
   authWBackendOk/authBackendReads (GetAllRoles is a batch: `Wb ∗ Wb`)/authWR; InvAuth
   ~1336-1625); batch Unlock `Wb ∗ Wb`, ForceCommit `Wb`, CreateAuthBuckets `Wb`
   (AuthSrv.lean `authSchemaSrv` ~81-106, and authSchemaSnap, AuthSnapKit.lean); at the server
   `Wb := backend.wbTok d.γB`; authSchemaSrv drops `ownToks d.γB.wb 2` (AuthSrv:91, and
   authStoreKit:195). Store methods that Unlock a batch (UserAdd(+_sure,_tieSure),
   UserChangePassword, UserDelete, UserGrantRole, UserRevokeRole, RoleAdd, RoleDelete,
   RoleGrantPermission, RoleRevokePermission, AuthEnable, AuthDisable, HasRole?, plus
   NewAuthStoreOn's boot: Create 1 + batch 2 + ForceCommit 1) take `Wb ∗ Wb` per batch (their
   specs, Spec/…/auth/authStore__*.lean, LatestTie's specT/specTB, and the step contracts
   `backendAuthSteps(X)` in apply/AuthSteps(X).lean).
   **Where the per-request tokens come from (found, not done):** the apply loop gets receipts at
   Go steps (`wp_go_step_receipt'`, EtcdServer__apply.lean:1443 takes the admin step's `⧗ 1`,
   passed as `Hlc` through `applyEntryNormal.specOn` → `adminEntryOn.spec` (AdminEntryOn.lean:76)
   → Apply.adminSpecL/uberAdmC (ApplyFnAdminL) → dispatch.adminSpec → AdminChain → fuelSpecX).
   Take two more receipts (and later credits: `srvWTPool_take_extra` needs `⧗ 1 ∗ £ 1` each;
   `srvWTPool_take_two`, InvApplier.lean:1523) at further Go steps there, convert to two
   `srvWT E` (= `bkWT d` = `wbTok d.γB` at the current backend, `apply.bkWT`, Contracts.lean:127),
   and thread them down that chain to the store call. Boot's 2 extra: from
   `□ (⧗ 1 ={⊤}=∗ wbTok)` (srvWTPool / srvWTStockInv) into `authKitIn`'s on row (AuthSrv:114),
   discharged by NewServer. Expect ~40 files; check `etc/importers.py --uses`.
2. **S1 option A** (unchanged from below; decided, not started).
3. The finish (notes, interfaces, tcb, collections + `irrDecode_utf8` in authkv's, gates, Freeze
   F1 section, full build), then STOP for 81's axiom re-review. Do not land.

### S1 option A (details, decided)

`auth.tpReady M` (`.on γa`: persistent one-shot "shot" at a new
   ghost name, e.g. a field of `AuthNames` or a name allocated with them; other modes `True`) in
   the info clause of `tokenProviderOkA`/`tokenProviderOk` (InvAuth ~740-790) and so in the store
   specs `authInfoFromToken`/`AuthInfoFromCtx`; `simpleWaitOk p` becomes
   `{{ tpReady }} iw idx {{ anyRecv }}`. NewServer (`NewServer.lean:778`, the `wp_func_lits`
   before `hTP`): persist the `srv` variable's points-to, allocate
   `inv (pending ∨ shot ∗ ∃ wt, srvApplyWaitAddr s ↦□ wt ∗ isWaitTime wt (appliedAtLeast γr))`,
   prove the closure's contract (load `srv`, open the inv for the field load, `isWaitTime`'s Wait,
   law `waitBcast ⊢ anyRecv`: two cases, `broadcast_chan_receive` / `closed_chan_receive` as in
   Perennial's `isContextDone_receive`, context/Base.lean:700); authSrvTP's pre (on mode) carries
   the waiter contract. `start` (`EtcdServer__start.lean:416`, where `isWaitTime_of_timeList` is
   made) fires the shot; the pending token reaches it through `isServerBuilt` (InvStart/InvBuild
   "Haw" rows); `tpReady` into `srvReadFieldsAt`'s on row; `isReqAuth`/`isReqAuthBound`
   (`etcdserver/InvRequest.lean` ~2660) gain the premise, their ~15 users supply it from the
   server's read view. STOP if a closed theorem's statement changes (81 expects none). Then
   AuthSrv `authSrvTP_on` drops `hValid`; Results `srv_auth_tp_on`/`server_new_auth_on`, authkv
   Results (exported, strictly stronger: CP).
Finish details: `notes/auth-validspec-false.md`, `notes/auth-schema-srv-refuted.md` status,
decisions.md entry, STATUS.md; `etc/gen-interface.py etc/api/<pkg>.txt`; tcb collections (authkv:
+ `irrDecode_utf8`); Freeze package F1 section.

## Build status (2026-11-12)

F4 targeted builds pass: auth Fuel/Boot and all store methods; apply AdminChain, DispatchAdmin,
Apply, ApplyFnAdmin, AuthFuel, AuthStepsX, DispatchKVL, authApplierV3__Apply, ApplyAdminL,
uberApplier__dispatch; etcdserver SnapAuthRecover; and the mid-level importers
(auth LatestTie/TieRes/NewAuthStoreOn, apply.Link, StoreLatest, AdminEntryOn, ApplyNormalOn,
EtcdServer__applyEntryNormal, UberOn, UberKit, SnapRecvOn, ApplyAllSnap: 5134 jobs, pass). AuthSrv and everything importing it (etcdserver Results/Link,
the examples) still fail on S1's `hValid` (expected until S1 option A).

## Pitfalls

- InvAuth's write/read contracts sit in hlc-generic sections in places; check the section before
  using hasLC-only vocabulary.
- `rbPart_none` takes the map explicitly: `backend.rbPart_none d.γB ∅`.
- Build: `export TMPDIR=/shared/tmp; systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-ddc.json <modules>`; full build under flock with etc/timed-build.py.
