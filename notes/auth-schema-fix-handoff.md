# auth-schema-fix: handoff (2026-11-12)

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

## Next, in order (81's decisions of 2026-11-12 in questions.md; F4/F1 first, they do not depend on S1)

1. **F4** (UTF-8 roles; nothing started). Trusted: UnsafePutUser's premise in `authBatchTxLkR`
   (InvAuth ~1399) and the store view `authBatchTxLk` (~1344) gains `∀ x ∈ ur.roles, utf8Valid x`
   (`Proof/unicode/utf8/Valid.lean:45`). Design found by reading (cheapest route):
   - `auth.rolesUtf8 st := ∀ u rs, st.users !! u = some rs → ∀ x ∈ rs, utf8Valid x` (Model.lean,
     beside `permKeysOk`, 289). Keep it in the history: `authHist` (Model.lean:399) holds
     `∀ st ∈ hs, permKeysOk st`; make it `permKeysOk st ∧ rolesUtf8 st`, or bundle as one
     predicate `stWf` and replace `permKeysOk` in authHist/`authOwnF_revCur_append`'s `hk`/
     `authOwnF_last_permKeysOk`/`authOwn_last_permKeysOk` (InvAuth 1729, 2329, 2437, 2475) by it:
     the pass-through sites (most of the 92 mentions, ~25 files: `grep -rn permKeysOk`) then
     change by name only; the constructors are Steps.lean:246-279 (`permKeysOk_putUser` needs the
     roles' UTF-8) and Boot.lean:38.
   - Store methods that put a user: UserAdd (roles `[]`), UserGrantRole (existing roles + `role`),
     UserRevokeRole/UserChangePassword/RoleDelete (subsets of existing roles: from `rolesUtf8` of
     `histLast`). The new role's UTF-8: add `utf8Valid role` to `stepOk` for the grant (or a
     premise of `UserGrantRole.spec`/`specTB`, LatestTie.lean:457, discharged in
     `apply/AuthFuel.lean:200` / `AuthSteps`/`AuthStepsX`). Off/any modes: `histLast` is any
     (disabled) state; the methods' other latest-state facts are already caller premises
     (`u.length < 2^62`), so take `rolesUtf8` the same way (a pure premise over `histLast`).
   - Supply: NEW trust-boundary law `apply.irrDecode_utf8` (beside `opaque irrDecode`,
     `etcdserver/apply/InvRequest.lean:178`): a decoded request's UserGrantRole role/user, UserAdd
     name, RoleAdd name are valid UTF-8. Go evidence: `/shared/tmp/auth-safe/fix-tests/
     irr_utf8_test.go` (passes). Also needed by the snapshot image's induction
     (`etcdserver/SnapAuthRecover.lean:121` `histWf`, 126 `hK`, 157-209): add `rolesUtf8` to
     `histWf`, the grant step needs the entry's decode law.
   - nonissue already written: `nonissues/etcd-auth-putuser-invalid-utf8-role.md`.
2. **F1** (plan step 5, decided): `Wb` parameter on the write contracts (authBatchTxLkR/OkR,
   authWBackendOkR and the store views); batch Unlock `Wb ∗ Wb`, ForceCommit `Wb`,
   CreateAuthBuckets `Wb`; at the server `Wb := backend.wbTok d.γB`; authSchemaSrv drops
   `ownToks d.γB.wb 2`; boot's 2 extra tokens from the server's write-back pool
   (`□ (⧗ 1 ={⊤}=∗ wbTok)`, srvWTPool/srvWTStockInv, receipts) into authStoreKit's on-mode
   `authKitIn`. ~17 store method specs take the per-batch charge.
3. **S1 option A** (decided): `auth.tpReady M` (`.on γa`: persistent one-shot "shot" at a new
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
4. Notes (`notes/auth-validspec-false.md`, `notes/auth-schema-srv-refuted.md` status, decisions.md
   entry, STATUS.md), interfaces (`etc/gen-interface.py etc/api/<pkg>.txt`), tcb collections
   (authkv: + `irrDecode_utf8`), Freeze package `/shared/tmp/auth-safe/freeze-fix.md` complete
   (F4 and F1 old → new with Go evidence); full build; STOP for 81's axiom re-review. Do not land.

## Pitfalls

- InvAuth's write/read contracts sit in hlc-generic sections in places; check the section before
  using hasLC-only vocabulary.
- `rbPart_none` takes the map explicitly: `backend.rbPart_none d.γB ∅`.
- Build: `export TMPDIR=/shared/tmp; systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-ddc.json <modules>`; full build under flock with etc/timed-build.py.
