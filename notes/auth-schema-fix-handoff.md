# auth-schema-fix: handoff (2026-11-13, fourth step: 81's NO GO, two MAJORs to fix)

## State (read this first)

Everything below "Finish done" was committed and passed the full build and gates (2cd0cf1d59), but
etcd-grove-81 said NO GO after an independent review: two MAJORs and a MINOR,
`notes/auth-unknown-fields-nested.md` (the finding, evidence, decisions). Not landed. Context ran
out for the third agent before starting the fixes; nothing of them is done.

## Next, in order (81's decisions, 2026-11-13)

1. **Permissions (MAJ-1, decision (1)).** Do NOT just put `unknownFields' := slice.nil` into
   `ownPermW`: it is also the request side's predicate (`roleGrantPermissionReqIs`,
   `auth/Requests.lean:116-122`; the client's `InvAuthConn.lean:124`, `PerTypeAuth.lean:258`), whose
   permission comes from decoding a client's request, which may carry (valid) unknown fields: fixing
   it nil there would make the decode claims false. Instead: a stored-permission predicate (e.g.
   `ownPermS`/`ownPermSX`, as `ownPermW`/`ownPermX` with `unknownFields' := slice.nil`) used in
   `ownRole`/`ownRoleX` (Buckets.lean ~128-185), `ownPermX_persist` adapted; RoleGrantPermission's
   fresh `newPerm` (store.go:839-842; proof `authStore__RoleGrantPermission.lean`, lemmas at ~75-170,
   ~240) builds the stored one; RoleRevokePermission (~262), getMergedPerms (~213), PermSorter (~81),
   Reads read it. Check that `Requests.lean`'s docstring line 7-8 ("puts into the role's record as it
   is") matches the code (store.go builds a new message) and fix it.
2. **Options (MAJ-2, decision (2)).** `UserRec` (auth/Buckets.lean or Model) gains the Options'
   raw unknown bytes (e.g. `optsUF : GoString`), with a premise that they are valid wire format (they
   came from gRPC's decode of the request); `userEncode` takes them (it is a function of the record);
   `userOptsAt o b uf'` ties the Options message's `unknownFields` to them (nil `o`: `[]`); 
   `userAddReqIs` carries them from the request (and the IRR decode side that produces it); every later
   put (ChangePassword, GrantRole, RevokeRole, RoleDelete) carries the stored value (they copy
   `user.Options`). Prefer this over a client-side premise. Go control: a `UserAddOptions` with valid
   unknown fields round-trips through UserAdd/GetUser and the read does not panic (adapt 81's
   `zz_review_optsuf_test.go`; put it in `/shared/tmp/auth-safe/fix-tests/`).
3. MINOR: `notes/auth-validspec-false.md` ("strictly stronger", the M3 paragraph): say R-M1 makes D22
   harder to meet on reads.
4. Record both in `notes/decisions.md` (auth-schema-fix section) and the Freeze package
   `/shared/tmp/auth-safe/freeze-fix.md` (old → new, Go evidence); update
   `notes/auth-unknown-fields-nested.md` to "fixed".
5. Full build, tcb --check, gates (commands in "Finish done" below), then STOP for 81's re-review.

---- older handoff below ----

# auth-schema-fix: handoff (2026-11-13, third agent: re-review changes done, finishing)

## State (read this first)

Branch `auth-schema-fix`. Since the previous handoff (below): lean 222c3fcff7 merged (f884b4616c;
STATUS one copy per entry, the oldest to status-history; examples/etcd/auth/Defs.lean merged without
conflict, `runsNoRequireLeader` gone); re-review changes committed: 9317630050 (M1 unknown fields nil in
`ownUser`/`ownRole`/`ownUserX`/`ownRoleX`, a trusted tightening; m1 `0 < name.length` in both put
clauses with `auth.namesOk` in `authSmall`/`stepOk`; m2 recorded for D22 in decisions.md),
8b20ea1ef3 (m3 authSchemaSrv's docstring; ValidSpec lens M1-M4). Go evidence for M1:
`/shared/tmp/auth-safe/fix-tests/zz_authfix_unknown_test.go` (passes; run in the clone
`/shared/tmp/authfix-81/etcd` at c90b03b56). Freeze package: `/shared/tmp/auth-safe/freeze-fix.md`
(sections R-M1, R-m1, R-m2). Forms: questions.md, last entry. Targeted builds pass (auth store
methods, Fuel/Boot/Token*, apply AuthFuel/AuthSteps(X)/Contracts, etcdserver SnapAuthRecover,
KVAuthModel, InvAuthBackend). The lost helper's 254a2a6e4f/8b5b18ab8b/d2519c5729 were not re-checked
separately: the full build, tcb --check and gates below check them.

## Finish done (2026-11-13), STOPPED for 81 before land.sh

Full build ok (17473 jobs, `/shared/tmp/authfix-81/full-build1.log`); etc/gates.sh all passed
(`/shared/tmp/authfix-81/gates1.log`: tcb 869 axioms, 4 sorries, matches baseline; 55 collections
match; interfaces ok, no interface diff: auth/etcdserver are not API packages). STATUS entry
rewritten (2026-11-13). Next: 81's go, then (GOWORK unset)
`LAKE_PACKAGES=/shared/tmp/manifest-ddc.json PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc etc/land.sh`
(merge lean first if it moved; recheck STATUS's ten entries and status-history's `wc -l`).

---- older handoff below ----

# auth-schema-fix: handoff (2026-11-13, after F1, S1 option A and the first finish)

## State (read this first)

Branch `auth-schema-fix` at the commit holding this note. Done and committed: F3, F2, F4, F1
(398c6dc09f, 10da96a817), S1 option A (d9f4a2dd66, with 81's accepted deviation: isReqAuth(Bound)
unchanged, pre-start holders carry `□ (auth.tpReady M -∗ …)`), nonissues index, trust base +1 axiom
`apply.irrDecode_utf8` with baseline and 17 collections updated (8b5b18ab8b), notes (d2519c5729:
auth-validspec-false fixed, decisions entry, STATUS entry). Freeze package complete:
`/shared/tmp/auth-safe/freeze-fix.md` (F1-F4, S1 sections). Not merged with lean, not landed. The
first finish's full build/gates results were not reported (the subagent was lost): redo them.

81's axiom re-review: READY WITH CHANGES, no blockers. Findings:
`/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_bbd42cc3-0cf/journal.jsonl`;
reviewers' Go tests `/shared/tmp/coord-81/authfix-rereview/`. Decisions in questions.md
("Axiom re-review (2026-11-13)"). 81 says: do them directly, no subagents.

## Next, in order

1. Merge lean (222c3fcff7 or later) early. Expect conflicts in examples/etcd/auth/Defs.lean (k8s 7f-4
   T-k / step 6 deleted runsNoRequireLeader from the etcdstart/auth Defs bundles) and STATUS.md (one
   copy per entry, ten in all; the oldest to status-history, which is APPEND-ONLY: `wc -l` at least
   lean's).
2. Unknown fields (trusted tightening): `ownUser`/`ownRole` on the PUT side (UnsafePutUser /
   UnsafePutRole clauses of authBatchTxLk(R), InvAuth.lean) require the message's unknown-fields slice
   empty (`uf ↦*□ []` or nil: look at how ownUser/ownRole expose `unknownFields`); the store meets it
   (messages built fresh, or from its own Unmarshal); UnmarshalUser/UnmarshalRole's specs give it for
   roleEncode/userEncode bytes. Freeze package: old → new and a Go test (adapt the reviewers'
   TestRereviewUnknownFields in /shared/tmp/coord-81/authfix-rereview/: an empty uf round-trips;
   protobuf-go leaves unknownFields nil decoding these bytes), at the server pin (GOWORK=off for the
   test only).
3. m1: `0 < name.length` in both put premises (UnsafePutUser, UnsafePutRole), with the store's
   "stored names are non-empty" fact (find or add it in the auth invariant / model).
4. m2: record the per-batch pend bound as a D22 plan item (notes; D22's plan section in decisions.md).
5. m3: authSchemaSrv's docstring (AuthSrv.lean ~60-80): the Wb charges, the lend as an observation,
   F1-F4 (it still lists "today's five refutations" in the old terms).
6. ValidSpec lens M1-M4 (details in the journal): newAuthStore_boot's readiness cell allocated at a
   fresh name (not reusing γt); token_simple_new's mode parameter as the reviewer suggests; the
   "strictly stronger" wording in notes/auth-validspec-false.md; stale ValidSpec comments
   (`grep -rn ValidSpec`), including the authkv link input (etc/link-*.txt or examples/etcd/auth).
7. Full build (flock /shared/tmp/etcd-grove-build.lock, systemd-run --scope -q -p MemoryMax=64G,
   etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json), tcb --check (collections only for
   exactly the intended changes), gates (etc/gates.sh's list; GOWORK unset), gen-interface
   (regenerate, list diffs). Then REPORT to 81 before etc/land.sh (the trusted tightening needs 81's
   look). Land command once 81 says go: LAKE_PACKAGES=/shared/tmp/manifest-ddc.json
   PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc etc/land.sh, GOWORK unset.

Answer already given to 81's question (S6): the branch does not restate the auth-off
`auth.NewAuthStore.spec` or its post (`git diff lean -- Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean`
empty); `AuthNames` gained a field `rdy` (not mentioned by that axiom).

---- older handoff below ----

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

## F1 in progress (2026-11-12, second agent)

Done, not committed until the auth package builds: InvAuth's contracts take `Wb` after `T`
(`authBatchTxLk(R)`/`authBatchTxOk(R)`/`authWBackendOk(R)`/`authBackendReads`/`authWR`): `Unlock`
`∗ Wb ∗ Wb`, `ForceCommit` `{{ T ∗ Wb }}`, `GetAllRoles` `∗ Wb ∗ Wb`. A subagent propagates it
through the auth package (store specs take `Wb ∗ Wb` per batch, AuthEnable/AuthDisable `Wb ∗ Wb ∗
Wb` with ForceCommit; boot 4; CreateAuthBuckets `{{ T ∗ Wb }}`).

Design for the apply and server layers (decided by the agent within 81's route; form only):
- apply/Chain.lean, beside `bkRTOf`: `bkWTFor E := ∃ d, ⌜∀ B, (E.BkTie B ⊢ ⌜B = d⌝)⌝ ∗ bkWT d`
  (a write-back token of whichever backend the tie names); a split lemma
  `mPre E c a info log Pre Q Post ∗ bkWTFor E ⊢ ∃ cr B, … ∗ bkWT B ∗ …` (B = d from the tie,
  `pure_and_sep` keeps `E.BkTie B`).
- isAuthSteps(X) take `Wb`; each method's pre `Wb ∗ Wb` (AuthEnable/AuthDisable 3, Authenticate 0);
  `backendAuthSteps(X) E p …` instantiate `Wb := bkWT B` under their `∀ B`.
- stepSpec/fuelSpec(X) take the count they need as `bkWTFor E` conjuncts; AdminChain/DispatchAdmin/
  ApplyFnAdmin(L)/Apply.adminSpecL/uberAdmC/AdminEntryOn take three (`bkWTFor E ∗ bkWTFor E ∗
  bkWTFor E`; the six on-mode admin requests: UserAdd, RoleAdd, UserGrantRole, RoleGrantPermission 2,
  AuthEnable 3, Authenticate 0), dropping the unused ones.
- Server: `srvWT E ⊢ bkWTFor E` (srvBkTie d B = ⌜B = d⌝); EtcdServer__apply's entry loop takes
  three more receipts (`wp_go_step_receipt'` at the `FuncResolve` of the later `hU64` calls, as at
  line ~1466) and `srvWTPool_take_extra`-style lemma over `srvApplyKVOn` (as `srvWTPool_take_nOn`,
  without the count) into three `srvWT E` for `applyEntryNormal.specOn` (on mode).
- The auth realization's Wb at the server: `backend.wbTok d.γB` (authSchemaSrv/authWAtHook/
  authSchemaSnap at their `d`); authApplyRes(At/B/Pre) carry `authWBackendOk … (authWTok T)
  (backend.wbTok d.γB)` with the row's `d` (authApplyRes/At: `∃ d` or the tie; check which way the
  conversions go before choosing).

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
