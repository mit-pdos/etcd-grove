# The server's migration onto mvcc's API (strict M1): hand-off

Scope: `server/v3/etcdserver` outside `txn/` and `api/`, and `server/v3/lease`. The frozen draft is
`notes/mvcc-api-clients/ServerSpecs.lean` (with `clients-server.md`); its names are kept, namespace
`srvApi`, a restated definition with the suffix `A`.

## Done

- **The lessor's specs restated** (`Spec/go_etcd_io/etcd/server/v3/lease/lessor__Revoke.lean`,
  `lessor__Grant.lean`): `lease.lessor.Revoke.spec` and `lease.lessor.Grant.spec` are the draft's
  `lessor.Revoke.specA`/`lessor.Grant.specA` word for word (Revoke: `mvccDeleter`, the backend share
  and frozen hook, `csContractA`, one nested update `auBegin γ σ₀ (auEnd γ σ₀ dels Y)`, the sort
  premise kept; Grant: only the contract). Both build.
- **The update shapes** (`Proof/go_etcd_io/etcd/server/v3/lease/MvccShapes.lean`): `stAt`,
  `auBegin`, `auRead`, `auEnd`, `auSnap`, `auCompact`, `auRestore`, `csContractA` (below the lessor,
  whose `Revoke` takes them). `auSnap` without the draft's `σ.crev = -1` (the API's
  `mvccImage_snapshot.law` dropped it; the draft's own header says the M1 proofs drop it). Builds.
- **The store invariant and its builders, proved** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/
  KVStoreCore.lean`, builds, no `sorry`): the invariant generic in the raft witness `Nx` and the
  permit `Cp` (`kvStoreInvG`; the draft's `kvStoreInv` is it at `kvNx γr on`, `crevOk γr`, by
  `rfl`), `KVSNames`, `kvsN`, `kvLogLb`, `wSt`, `crOwn`, and every builder over mvcc's
  `persistent.law` and `mvccState_reachable.law` as hypotheses: `au_begin`, `au_wread`, `au_snap`,
  `au_end` (the two nested updates: the notify step moves the pending halves and the notified log,
  its receipt mvcc's; the commit step the committed log), `au_compact` (the compaction revision's
  three parts), `au_restore`, `au_read` (`kvReadAt`: floor, witness, receipt by `preceipt_mono`,
  reachability), `writer_facts`, `kvAusG` (all together, `kvAus.law`'s shape), `kvPeekG`,
  `histLb_bootG` (a reachable state's logs begin with `[[], []]`, `reach_prefix`), `bootStoreG`
  (`⧖ 0` by `preceipt_zero`). The riskiest part of the server's side: no frozen statement found
  false.
- **The draft's statements** (`KVStoreApi.lean`: §2-§3d, §4 as `AEnvA` etc., §6) and their laws by
  instantiation (`KVStoreLaws.lean`: `kvAus_holds`, `kvPeek_holds`, `crevOk_off_holds`,
  `histLb_boot_holds`, `bootStore_holds`). **Not built yet**: their imports (`ServerOn`,
  `InvImage`, `apply.Chain`) are red under strict M1 (`apply.Chain` and `apply.Contracts` use txn's
  deleted sole-writer API: `txn.kvWriter`, `txn.Writer`), so the statements are the draft's text,
  typechecked at `6cc29c14f0` by the draft's author, and the laws' proofs are one-line
  instantiations of the core's, which builds.

- **The lessor's writes over the API's `hookRun`** (by reference, builds): `leaseBatchTx`'s
  `LockInsideApply` takes `csContractA P g …` at the hook `g` whose value its `f` is
  (`⌜f = #g⌝ →`), so that a `nil` hook is the caller's view shift; `Lease.persistTo.spec` and
  `lessor.Checkpoint.spec` restated like `Grant` (`f : GoFunc`, `lessorBackend … #f`,
  `csContractA`); `lessor.Grant.wp_proof`, `lessor.Checkpoint.wp_proof`, `Lease.persistTo.wp_proof`
  proved over them (no `sorry`).

- **The apply chain's foundations, restated in place** (builds: `apply.Contracts`, `apply.Chain`,
  `apply.InvUber`, `InvRequest`, `WorkloadDefs`, and every `Spec/.../etcdserver/apply/*.lean`):
  - `apply.AEnv` has the draft's `AEnvA` fields (`kv`, `γ : MvccName`, `γs`, `Nx`, `Pk : BkRef →
    IProp`, `f : GoFunc`, ..., `Cp`, `BkTie`); `kvOwn`, `mPre`, `certPre` (`E.Nx`), `cmpOwn`,
    `leasesLive`, `envAus`, `kvBk`, `cmpChan` as drafted; `KVStoreApi.lean`'s `AEnvA`, `kvOwnA`,
    ... are aliases of them.
  - Choices "by reference" (the coordinator's decisions where given): `threadTok` beside `kvOwn` in
    the KV, revoke and compaction triples (pre and post); the floors `kvLogLb E.γs F` in place of
    `idxCert`; `putPre`/`deletePre`/`txnPre`/`revokePre` without `storeWT`, `txnPre` at txn's
    `TxnPreA`, `rangeOk` without `sortOk` (txn's restated specs); `cmpAdmitRev log rev` = `1 ≤ rev ∧
    rev < |log|` (no mode); `cmpTriple` at `E.Cp` with `threadTok` and, through a compacting chain,
    `cmpChan`; `revokeRes` over `rdOwn`/`mvccDeleter`; the components' contracts (`isAuthStore`,
    `isAlarmStore`, `isCluster`, `isApplyLessor`) over `Pk B`, `f`, the tie `BT`, and the backend
    `B`'s `bkWT B`/`bkRT B` (`backend.wbTok`, `rdTok ∗ bOpen`) per write; the chain's methods whose
    components write (`respMethods`, `resp0Methods`) take `mPreW` (mPre with `bkWT B ∗ bkRT B` at
    the same `B`) and give `mPostW`; the cluster's `mPreV` carries them too; `uberApplier.Apply` and
    `dispatch` take `kvOwnPre v3 E log Pre Q Post` (the KV resources with the contract at `kvBk`'s
    backend) and give back `threadTok`, a reader token; `applierV3backend.newHeader` at the
    thread's token and the writer's half; `isApplyKV kv γ := □ isMvcc kv γ`.
  - `srvFloorFacts` over the store's committed-log lower bounds (`slog`, the draft's
    `srvFloorFactsA`); `resultIs`/`srvAppliedBody` over `kvLogLb`, `resultIsW`'s certificate
    `E.Nx`.
  - `kvModelM` moved from `ServerOn` to `KVModelM.lean`; the draft's read-path definitions
    (`srvRdCallA`, `rangeReadOkA`, `newHeaderPostA`, `logOk_of_receipt`, ...) to `KVStoreRead.lean`.

- **Step 1 of the hand-off, done (2026-11-05, second session; builds, no `sorry`)**: `InvProposer`,
  `InvApplier`, `KVModel`, `KVApply`, `KVChainOff`, `KVAuthModel`, `KVModelM`, `InvImage`,
  `KVStoreApi`, `KVStoreLaws`, `apply.AuthDerive`, `apply.AuthLemmas`, `apply.AuthSteps`. Choices:
  - `srvKVInvs E γr` (in `isServer`'s atomics) is `kvInv ∗ kvCertInv ∗ srvRaftLogInv ∗
    □ kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ∗ ⌜cmp, cret ties ∧ envWitOk E⌝`: the draft's
    `srvKVInvsA` without its ties of `E.kv`/`E.Nx`/`E.Cp` (they name `kvNx`, which needs the KV
    model, above `InvApplier`), the store invariant boxed (its persistence is the API's
    `persistent.law`, `isMvcc` being sealed), `envWitOk E` (the witness and permit persistent and
    timeless, what `writer_facts` needs). `kvCertInv` (the server's own KV certificates' ghost
    state) is kept: `kvApplied` still carries `kvCert`; removing it is a later cleanup.
    `KVStoreLaws`: `srvKVInvsA_of` (`srvKVInvs` and the ties give the draft's `srvKVInvsA`),
    `srvKVInvs_of` (the converse direction's builder, at `kvNx`/`crevOk`, with `kvCertInv`),
    `kvNx_off` (`kvNx γr false = kvNxOff`, `rfl`), `envWitOk_srv`.
  - **The backend over `BkRef`.** An epoch's environment fixes its backend through the tie:
    `E.BkTie = srvBkTie B` (`⌜B' = B⌝`), in `srvEnvOk` (in place of `E.γ.kb = some d`; the two mode
    clauses `E.γ.cm = E.cmp`, `d.cm = E.cmp` dropped: the API's backend always compacts, the store
    has no mode; `srvEnvOk_kbCmp`/`_cm`/`_off` deleted, 3 users outside step 1). `srvFieldsAt`:
    `E.Pk = fun _ => batchLockInv γ TM ∧ v.hook = #E.f`. `srvBeHooked` at `mvccW gx` (∃ gx),
    `srvBeRO B := ∃ gx Pk, isBackend … (mvccW gx) Pk B.b`.
  - **`E.γbe` records `bkKey B = (B.γB, B.b)`**, not the backend: a `BkRef`'s parameters hold
    functions (not `Pos.Countable`), so agreement gives the names and location, not `P`. Enough for
    the write budget (`srvWTStockInv` uses only `B.γB`). **Open**: the storage-version monitor's
    checkout of `bkRT d` from `srvWTPool` gets the invariant's `d.P`; a proof that needs it equal to
    its own backend's `P` needs `P` fixed (it is server-wide: `applySnapshot` keeps `d'.P = d.P`).
  - `srvWT E` (`∃ d, ⌜E.BkTie = srvBkTie d⌝ ∗ bkWT d`) in place of `mvcc.storeWT E.γ` in the
    budget's takes; `wbSupply_of_stock` (a backend-level supply) in place of `kbWTSupplyM_of_stock`.
  - `srvApplyKV_writer` (in place of `srvApplyKV_idxCert`) and `srvApplyKV_small` (now a fupd)
    take mvcc's `persistent.law`, `mvccState_reachable.law` (and `receiptBound GF ≤ 2 ^ 48` for the
    small log) and `srvKVInvs`; `KVStoreCore.reach_len_logCh` (a reachable log has a revision per
    change past its first two) replaces the sole writer's time receipts.
  - `KVApply`: `kvNxOff γ γk l` (the off mode's raft witness, `= kvNx γr false`) replaces mvcc's
    `certOk` (`kvCert_certOk` → `kvAppliedL_nx`); `kv_certPre` takes `E.Nx = kvNxOff γ γk`;
    `kv_cert_floor` takes `kvNxOff` (no `kvCertInv`, `γs`, `hγ`, `hx2`); `kvEntry_len` takes
    `x.log.length + 3 ≤ 2 ^ 63` (the writer's facts; `TxnPreA` has no size clause).
  - `AuthSteps`: `isAuthSteps st P (f : GoFunc)` over `csContractA`; `backendAuthSteps` at every
    backend's lock (`□ ∀ B, isAuthSteps … (E.Pk B) E.f …`); the step specs take and give
    `threadTok` (`newHeader`'s); `mPre_split`; `isAuthSteps_of_authInv` takes `f ≠ func.nil` and
    bridges to the auth store's specs, still over mvcc's internal `mvcc.csContract P #f`
    (`csContractA_old`; the auth package is outside this track).
  - `AuthLemmas`: `txnPermT`/`checkTxnReqs_of` at `MvccName`, `Pk`, `f : GoFunc`, `BT` (as
    `checkTxnPermission.spec`); the rejection lemmas take `csContractA P E.f` at any `P`.
  - Still on mvcc's internals but building (not API): `KVLemmas.kv_cert_read` (`mvcc.certOk`),
    `InvImage` (`mvcc.keyImageM`, pure).

- **Step 2 started (second session): the backend's writing methods proved over the API** (no
  `sorry`): `applierV3backend.{Alarm, AuthStatus, AuthEnable, AuthDisable, Authenticate, LeaseGrant,
  LeaseCheckpoint, UserAdd, UserDelete, UserChangePassword, UserGrantRole, UserRevokeRole, UserGet,
  UserList, RoleAdd, RoleDelete, RoleGet, RoleList, RoleGrantPermission, RoleRevokePermission}`,
  over `apply/WriteLemmas.lean` (`mPreW_split`: the writer's half, the contract at `B`'s lock,
  `bkWT B`/`bkRT B`/`E.BkTie B`, the chain's resources, `kvRest`; `mPostW_backend`,
  `kvOwn_of_split`). Choice (by reference, the draft's rule "threadTok beside the chain's KV
  resources"): **every chain method that calls `newHeader` takes and gives `threadTok`** (its spec
  has `threadTok ∗` before `mPre`/`mPreW`/`kvOwn`/`revokePre` and before the post's
  `mPost`/`mPostW`/`kvOwn`/`kvPost`): the 20 `applierV3backend` specs above (but `Alarm`) and
  `LeaseRevoke`, the wrappers `authApplierV3.{UserGet, RoleGet, LeaseRevoke}`,
  `applierV3Capped.LeaseGrant`, `applierV3Corrupt.{LeaseGrant, LeaseRevoke}`,
  `quotaApplierV3.LeaseGrant`, `uberApplier.Alarm`, and `applierSpec`'s generic triples of
  `respMethods`, `resp0Methods` and `AuthStatus` (`Chain.lean`). Until then those specs had none,
  and `newHeader.spec` (restated at the thread's token) was not callable from them.
- Also proved: the cluster methods `applierV3backend.{ClusterVersionSet, ClusterMemberAttrSet,
  DowngradeInfoSet}` over `mPreV` (`WriteLemmas.mPreV_split`, `mPostV_of`).
- **Step 2 continued (third session, 2026-11-05)**, each building:
  - `applierV3backend.Compaction` (no `sorry`): `KV.Compact.contract`/`KV.Range.contract` at the KV's
    type from `shapes.law` (hypotheses `context.TODO`, `traceutil.EnsureTrace`, `shapes`), the
    update by `envAus`'s compaction builder (`CompactArm.wSt_crOwn_agree`: the writer's half and
    the compaction right at one revision), `commitReq_true`, `mvccInit`'s `ErrCompacted`;
    `ErrFutureRev` excluded by `cmpAdmitRev`.
  - `applierV3backend.newHeader` (no `sorry`): `KV.Rev.contract` at the writer's read update
    (hypothesis `shapes`, in place of `mvcc.store.Rev`).
  - `applierV3backend.{Put, DeleteRange, Range}` (no `sorry`), over txn's restated specs (hypotheses
    `context.TODO` and txn's `Put`/`DeleteRange`/`Range`), their updates built from `envAus`
    (`apply/KVBuild.lean`: `beginAU_of_auBegin`, `auEnd_wand`, `auRead_wand`, `commitAU_of_auEnd`);
    `Put`'s update only for a live lease (txn's `if decide …`), the writer's half kept otherwise.
  - `applierV3backend.Txn`, over `Txn.specSole`, **one `M1-REPLACE`** (see "Found", third session).
  - `applierV3backend.LeaseRevoke`, over `revokeClause`, **one `M1-REPLACE`** (see "Found").
  - `AuthSteps` over auth's restated specs (the auth track's `cca7e9a4a9`): `csContractA_old` and
    `isAuthSteps_of_authInv`'s `hf` deleted (its callers `Results.lean`, `AuthSrv`, `ApplyNormalOn`
    drop the `hf` argument when they are migrated).
- **Choices (third session)**, minor, the draft leaving them open:
  - `envAus` gains a last conjunct, **the writer's floor** `∀ log c F, wSt E.γs log c -∗
    kvLogLb E.γs F ={⊤}=∗ wSt E.γs log c ∗ ⌜F <+: log⌝` (`KVStoreCore.writer_floor`, proved over the
    store invariant): the KV methods' `kvPostF` floor `floorOkO`, which the sole writer's pin gave
    until M1. Whoever builds `envAus` (from `kvAusG`) adds `writer_floor`.
  - `applierV3backend.Range.spec` takes and gives `threadTok` (`KV.Range`'s; `applierTriples`' Range
    triple already had it).
  - `appliedHdr`'s room is `+3` (the writer's facts'; the draft's relaxation of `putOk`/`delOk`;
    `TxnPreA` has no size clause). Breaks v3rpc's `ServerKV.lean:563` (`Hlen.2` at `+4`), outside
    this track.
  - `revokePre`'s pure part takes `(stateAfter log).length ≤ 2 ^ 62` (the lessor's sort premise in
    `revokeClause`; the server derives it from `srvApplyKV_small`).
- **The wrappers, proved (third session, no `sorry`)**: corrupt `{Put, DeleteRange, Txn, Range,
  LeaseRevoke, LeaseGrant}`, capped `{Put, LeaseGrant, Txn}`, quota `{Put, Txn, LeaseGrant}`, auth
  `{Put, Txn, DeleteRange, Range, LeaseRevoke, UserGet, RoleGet}`, `uberApplier.Alarm`,
  `newApplierV3Backend`, over `apply/WriteLemmas.lean`'s splits of `mPre`/`mPreW` into the chain's
  resources and the rest (`mPreRest`, `mPreWRest`: `_split_chain`, `_of_rest`, `_reject`,
  `_reject_cs`, `_lend`, `_rd`). `authApplierV3.Range.spec` and `applierV3Corrupt.Range.spec` take
  and give `threadTok` (as the backend's).
- **The constructors, proved (third session, no `sorry`)**: `newApplierV3Capped`,
  `newApplierV3Corrupt`, `newAuthApplierV3`, `newQuotaApplierV3`, `newApplierV3` (`WriteLemmas`:
  `mPreVRest`, `mPreV_split_chain`, `mPreV_of_rest` for the cluster methods' pass-throughs). So every
  `apply/` spec proof but `uberApplier.{Apply, dispatch}` builds over the API (with the two
  placeholders above).
- **Fourth session (2026-11-06)**, each building, no `sorry`:
  - **The two decisions** ("Decisions (2026-11-06)" below): `LeaseRevoke` and `Txn` discharged.
  - **`uberApplier.dispatch` and `uberApplier.Apply`** over `kvOwnPre` and the thread's token
    (`WriteLemmas`: `kvOwnPre_kvOwn` for the reads, `AuthStatus` and the requests with nothing to
    do, giving `kvOwn ∗ (∃ B, bkRT B) ∗ Pre`; `kvOwnPre_mPre` for `Put`/`DeleteRange`/`Txn`/
    `Compaction`, the write-back token dropped, the reader token aside; `kvOwnPre_mPreV` for the
    cluster methods (`kvOwnPre` is `mPreVRest`, by `rfl`); `rdLend_kvOwnPre`). So **every `apply/`
    spec proof builds over the API, no `sorry`**.
  - **`lease.lessor.Revoke`** (step 3) over the restated spec: `rd()` by `mvccDeleter` at the
    caller's begin update (`R σ := ⌜σ = σ₀⌝ ∗ auEnd …`, `subst σ`), each `Txn.DeleteRange(key, nil)`
    by `Txn.DeleteRange.contract` at the transaction's dynamic type (`shapes.law`'s third conjunct,
    `persistent_entails_right`), the key alone by `txn.logOk_of_del` on the call's post then
    `txn.delKeys_eq`; `le.b.BatchTx()` by `backend.backend.BatchTx.spec` over
    `mvccBackend_isBackend.law`; `UnsafeDeleteLease` with its callback from `mvccTxn_leaseDelete.law`,
    whose `End` triple runs at the caller's end update (`rw [hD]`: the deletions are the sorted
    keys'). Hypotheses: `hKeys hSort hUDL hBT hsh hisB hLD` (was `hKeys hSort hUDL hDel hEnd`).
  - **v3rpc's path (the coordinator's priority, 2026-11-06)**: `InvRead` restated (the draft's read
    path; choices below), `KVApplyOn`, `InvApRes`, `apply.AuthFuel`, `apply.AuthApplyLatest`,
    `AuthApplyRes`; `KVStoreRead` builds over them; `AuthReqDerive`'s `InvRead` import dropped.
- **Choices (fourth session)**, minor:
  - `InvRead`: `srvReadFieldsAt`'s KV is `□ isMvcc v.kv E.γ ∗ ⌜v.kv = E.kv⌝` (boxed: `persistent.law`),
    the `ReadView` field and its conjuncts gone (the API's `KV.Rev.contract` is on the handle), the
    lessor and auth store at `E.Pk`/`E.BkTie`, the floor `kvLogLb E.γs log₀`; `storeSmall` (and
    `storeSmall_of_receipts`, `_of_read`, `_small`) **deleted** (every sort's premise is txn's
    `stateOk`; the size facts come from the receipts, `logOk_of_receipt`); `srvRdCall` is the draft's
    `srvRdCallA`; `rangeReadOk`/`txnReadOk` are the draft's `rangeReadOkA` at the mode off but with
    the witness **`E.Nx log`** in place of `kvNx γr on log` (the two are equal by `srvKVInvsA`'s tie;
    `E.Nx` is what `kvReadAt` gives from `srvKVInvs`, and `InvRead` need not import the KV model's
    `kvNx`), with `⧖ (logCh log)` and `LogWf' log`; `txnAppliedOk` as `InvRequest`'s `resultIsW`
    (`kvLogLb`, `E.Nx`); `readIndexOk_logR` over the floors (`mono_list_lb_valid`). `isServerRead`
    now needs mvcc's `Assumptions` (`isMvcc`).
  - `KVApplyOn.srvKVInvsOn`: as step 1's `srvKVInvs`, `□ kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ∗
    ⌜envWitOk E⌝` in place of `⌜E.γ.cok = γr.kv.cok⌝ ∗ crevPermIs`.
  - `InvApRes`: `srvApplyKV_rt`, `srvApplyKV_ua_rt` deleted (mvcc's `storeRT` was the sole writer's);
    `srvApplyKV_ua_rt_pool` restated as `srvApplyKV_ua_pool` (the uber-applier and the backend's
    reader pool `bkRPool d.γB d.P d.b`, `d` the tie's): a backend reader token comes from the pool.
  - `AuthFuel`'s fuel specs take and give `threadTok` (as `AuthSteps`' step specs);
    `AuthApplyLatest`'s `Range.specL`/`DeleteRange.specL` take and give `threadTok`, `DeleteRange`'s
    floor `kvLogLb`, `certPreW` over `E.Nx`, `put/delete/txnPreW` without `storeWT` (`txnPreW` at
    `TxnPreA`), `auth_reject_kvPostFL` at any batch-lock invariant `P` (as `auth_reject_kvPostF`).
- **Fifth session (2026-11-06)**, each building, no `sorry` (commits `2af9be0883`, `539bc3eed8`,
  `726ac24773` and later):
  - **`ReadOn` builds** (v3rpc's path), with `EtcdServer.Range.spec` (statement only).
  - **The coordinator's decision on `KVRead.readWit_fire`, applied**: the tie of the witness is a
    pure conjunct of `srvKVInvs` (`⌜E.Nx = kvNxOff γr.raft γr.kv⌝`, its last; `kvNxOff` moved to
    `InvRequest`, beside `kvModel`, so that `InvApplier` can name it) and of `srvKVInvsOn`
    (`⌜E.Nx = kvNxOn γr.raft γr.kv st₀⌝`, `kvNxOn` new in `KVApplyOn`; `kvNx γr true` at
    `srvAuthSt0`, by `rfl`). In `srvKVInvs`, not `srvEnvOk`: `srvKVInvs` has `γr`, and is in both
    `isServer`'s atomics and `isServerRead`. `KVLemmas.kv_read_log` and `ReadOn.kv_read_logOn` are
    over the witness (`kvLogAt -∗ kvNxOff/kvNxOn l`): no certificates' invariant, no short-log case.
    `KVStoreLaws.srvKVInvs_of` is at the mode off (`hNx : E.Nx = kvNx γr false`).
  - **`ServerOnDefs.lean` (new)**: `ServerOn`'s mode-indexed read-side vocabulary split off
    (`kvLogAtM`, `kvLogsOkM`, `appliedPubM`, `kvLogsPubM`, `srvAppliedBodyM`, `srvAppliedInvM`,
    `srvUberBase`, `srvLessorNil`, `srvUberOn`, `srvKVInvsM` and its lemmas, `kvCertInvM`; from
    `AppliedOn`, `kvLogsPubM_ok`, `appliedLogAt_kvLogAtM`), unchanged but for the restatements
    below, so that `ReadOn` and `ReqOn` import it and not the built part and the boot (`InvBuild`,
    `BuildGap`, `BuildAlloc`, through `ServerOn`). `ReadOn` no longer imports `ServerOn`/`AppliedOn`
    (it imports `ServerOnDefs`, `read.Inv`); `EtcdServer__Range` imports `ReqOn` itself.
  - `ReadOn` restated as `InvRead` was: `srvReadFieldsAtM` over the store handle and `kvLogLb`;
    `rangeReadOkM`/`txnReadOkM` with `E.Nx log`, `⧖ (logCh log)`, `LogWf'`; `srvKVCoreM true` at
    `□ kvStoreInvG … ∗ ⌜envWitOk E⌝ ∗ ⌜E.Nx = kvNxOn …⌝`; **`srvKVCoreM_fire`,
    `srvKVCoreM_keys`, `readM_keys`, `read_keys` take the witness `E.Nx L` alone** (no sealed logs,
    no `certOk`, no floor `B`: the witness is a committed raft log's model); `readIndexOk_logM/RM`,
    `readServed_logRM` over `kvLogLb`; `readWit_fireOn` over `E.Nx l`; **`srvKVCoreM_cperm`
    deleted** (mvcc's `crevPermIs` is gone; its one user, client/v3's `InvWatch`, is outside).
  - `ReqOn`'s results (`resultIsWOn`, `resPostM`, `appliedOkM`) over `kvLogLb E.γs` and `E.Nx`, as
    `resultIsW`; `srvAppliedBodyM` over `kvLogLb`.
  - `srvUberOn`/`srvUberOn_adm` and `StoreLatest.srvAuthApplyResB` at **the epoch's one batch-lock
    invariant**: `∃ Pk, ⌜E.Pk = fun _ => Pk⌝ ∗ …` (as `srvFieldsAt`'s `E.Pk = fun _ => batchLockInv γ
    TM`), the admin steps at `Pk`; `StoreLatest` at `f : GoFunc`, `BkRef` (the auth track's list).
  - `KVRead` (`readServed_logR` over `kvLogLb`), `InvApplyAll` (`bemuP` over `BkRef`/`bkKey`;
    `AEnv.onBe E BT Pk f ciC RO RW` sets the tie, the lock's invariant, the hook, keeps `kv`, `γ`, `γs`,
    `Nx`, `Cp`: the store is restored in place), `apply.AdminChain` (`adminTriples` at `threadTok`),
    `apply.AuthApplyLatestTxn` (`Txn.specL` at `threadTok` and `kvLogLb`), the apply package's
    `DispatchKVL`, `ApplyKVL`, `ApplyFnKVL`, `DispatchAdmin`, `ApplyAdmin`, `ApplyFnAdmin`,
    `ApplyAdminL`, `ApplyFnAdminL` (`kvOwnPre ∗ threadTok` in, `threadTok ∗ (∃ B, bkRT B)` out, as
    `dispatch.spec`/`Apply.spec`; `Apply.kvSpecL`/`adminSpec` take `uberOwn ∗ kvOwnPre ∗ cmpOwn` in
    place of the hook's triple and `applyKV`: whoever calls them builds `kvOwnPre`).
  - **`SnapRO`**: the stores' contracts (`alarmApplyOk`, `authApplyOkM`, `authApplyOk`,
    `clusterApplyOk`, `lessorApplyOk`) for every `d : BkRef` at `srvBkTie d` and `fun _ => Pk` (in
    place of `∀ γ, γ.kb = some d`); `lessorApplyOk`'s reader `apply.bkRT d`; `authRecoverOk` over
    `BkRef`; `srvRestOwnH_lens_revoke` gives `rbPart … (· = leaseName) ∗ ⌜leaseParams⌝ ∗ lessorBeOn`
    (what `lessor.Revoke.spec` takes) in place of `storeRb`; `srvSnapRO` over `BkRef` (the tie), the
    KV `srvKVAddr s ↦□ E.kv ∗ □ isMvcc E.kv E.γ`, the lessor at `mvccLeases E.γ`, without the
    backend's mode and the watch flag; `srvSnapRO_succ` at the ties (`srvBkTie_inj`, new);
    **`srvKVCloser`, `srvKVCloserW`, `srvKVCloserW_off` deleted**, `srvSnapRes` without the closer
    (`Restore` takes `mvccOpen`, the apply thread's `cmpOwn`). The restated contracts are those of
    trust-boundary axioms (`v3alarm.NewAlarmStore.spec`, `auth.NewAuthStore.spec`,
    `lease.NewLessor.spec`, `EtcdServer.restoreAlarms.spec`): the same contracts at the API's
    vocabulary, for review when those specs are restated (not yet).
  - `InvRun`, `InvStart` (`srvFieldsBuilt`, `srvReadBuilt` as `srvFieldsAt`/`srvReadFieldsAt`),
    `InvBuild` (**`envAgree E E' := E.γs = E'.γs ∧ E.Nx = E'.Nx ∧ E.γrev = E'.γrev ∧ E.cmp =
    E'.cmp`**: what `srvC` reads; `envAgree_mode`/`_off`/`_on` deleted, the store having no mode;
    the draft's "every field but `kv`, `γ`, `Nx`, `Pk`, `Cp`, `BkTie`" would not give `srvC_agree`,
    whose results name `E.Nx`), `BuildGap`, `BuildAlloc` (`srvIndices_alloc` over `kvLogLb`),
    `ServerOn` (`srvBuiltG`'s KV row the store handle, `#Hsmall` gone).
  - Request-path statements restated (not yet built or proved): `EtcdServer.{Txn, Put,
    DeleteRange}.spec` (the floor `kvLogLb E.γs F`; `Put`/`DeleteRange`'s post `kvLogLb E.γs x'.log ∗
    … ∗ E.Nx x'.log`), `setAppliedIndex` (`kvLogLb`), `applyEntryNormal` (`srvWT E`), `applyAll`,
    `snapshot` (the KV row the store handle), `applyConfChange` (`BkRef` at the tie, `bkWT d`/`bkRT d`,
    `hookRun (E.Pk d) E.f`).
- **Next**: see "Left (sixth session)" below.
## Left (sixth session, 2026-11-06; in order)

**Stopped by the API's restatement.** Mid-session the mvcc track began restating mvcc's API over its
storage abstraction (the user's decision, `notes/decisions.md`, "mvcc's API over its storage
abstraction, not etcd's backend"): uncommitted `Api.lean`/`ApiState.lean` edits replace `BkRef` by an
opaque `MvccStorage`, `mvccBackendFor` by `mvccStorageFor`, drop `mvccW`/`backendRest`/`mvccImage`,
and `KVStoreCore` (so every module above it) no longer builds against them. Everything below was
built against the API as of `c472039823`; once the new API lands, the server's `BkRef`-shaped
vocabulary (`apply.bkWT`/`bkRT` over `B.γB`/`B.b`, `srvBkTie`, `srvBeOwn`, `srvWTStockInv`) has to be
restated over `MvccStorage` (the server keeps etcd's backend facts through the bridge,
`bridgeParams d.P`, as the decision says).

**Done (this session):**
- **The apply thread's reader token** (item 1's question, settled as proposed): `srvBeOwn` holds
  `apply.bkRT d` of the tie's backend (so `srvApplyKV`, `srvApplyKVCore`, `srvApplyKVOn` all carry
  it); `srvBeOwn_pool` lends it with the pool, `srvApplyKV_ua_rt_pool`/`srvApplyKV_ua_rt` (and the
  `On` ones) in place of `srvApplyKV_ua_pool`. **Found and fixed (the chain's own specs):** the chain
  gave the token back as `∃ B, bkRT B`, which loses the backend, so the apply thread could not lend
  it to the next entry. Now `apply.bkRTOf E := ∃ B, ⌜tieOk E B⌝ ∗ bkRT B` (`tieOk E B := ¬ (E.BkTie B
  ⊢ False)`, derivable from the tie, `tieOk_of`/`bkRTOf_intro`), in `mPostW`, `mPostV`, `dispatch`'s
  and `Apply`'s posts and `WriteLemmas`' builders; at the server's tie `bkRTOf_srv : bkRTOf E ⊢ bkRT
  d` (`tieOk_srv`). All the apply package's modules rebuilt (but `ApplyRec`, below).
  Where the slot comes from is still to write: one slot of `backend.rdStock` at `NewServer` (step 3),
  the new backend's at `applySnapshot` (step 4), the old backend's token to the closing goroutine.
- Building: `ApplyEntryOn`, `ApplyKVCore`, `StartOn`, `apply.UberAdmLBase`, `UberOn`, `ApplyNormalOn`,
  `UberKit`, `ModeSpecs`, `EtcdServer__apply` (both modes), `KVOutcomeOn`; applyAll's spec.
- `ApplyNormalOn`: `kvEntryOn_len` at the writer's room `+ 3`; `kv_certPre_keep` over `kvNxOn`;
  `srvAuthApplyResB_open`/`srv_uberAuthStepsL_at` at the epoch's batch-lock invariant `Pk`
  (`E.Pk = fun _ => Pk`); `srvApplyKVOn_writer`/`srvApplyKVOn_authOn` in place of `_idxCert`;
  `srvApplyKVOn_small` over the writer's facts.
- **Premises strengthened (the server's own specs):** `EtcdServer.apply.spec`, `applyEntries.spec`
  (and `ModeSpecs`' `specOff`s) take `receiptBound GF ≤ 2 ^ 48` in both modes (was: with auth on
  only): the log's smallness now comes from the writer's receipt (`srvApplyKV_small`), bounded only
  under it (until M1 the sole writer's receipts carried their own bound). `applyAll.specBatch` and
  `run` will need the same premise (NewServer has it). `EtcdServer.apply.wp_proof(Off/On)` take
  mvcc's `persistent.law`/`mvccState_reachable.law` (and `mvcc.Assumptions`), for the writer's facts.
- `srvFieldsAt` (and `srvFieldsAtM`, `InvBuild`'s, `InvStart`'s) record `E.f ≠ func.nil` (the
  server's hook is `getTxPostLockInsideApplyHook`'s closure): `mvcc.api.hookRun` at a non-nil hook is
  the triple `hookSpec` gives. `NewServer`/`applySnapshot` must supply it.
- `srvBkTie_inj` moved from `SnapRO` to `InvApplier`; `srvWT_at : E.BkTie = srvBkTie d → srvWT E ⊢
  bkWT d`.
- `apply.Apply.specRec` restated (`apply.bkToks v3 E Pre Q Post`: for the tie's backend its tokens
  and hook run, `kvOwnPre_of_toks`; `threadTok`; `bkRTOf E` back; the floor `kvLogLb`; `cmpAdmit` at
  the log), `spec_rec` adapted: **not checked** (committed `0255e5d962` after the API began to move).

**Left, in order (after the API's restatement is adapted to):** check `ApplyRec`;
`EtcdServer__applyEntryNormal` (the server builds `bkToks` from `srvApplyKV_ua_rt`, `srvWT_at`,
`hookSpec` with `E.f ≠ nil`; gives `bkRTOf_srv`'s token back; `srvApplyKV(On)_writer` for the floor;
`kv_certPre_keep`'s new arguments); then `ApplyAllSnap`, `applyAll` (with `receiptBound` above), and
items 2-5 of "Left (fifth session)".

**Placeholders:** none added. No axiom.

## Left (fifth session, 2026-11-06; in order)

1. **The red layer below `applyAll`** (step 2). Built since the fifth session's last commit:
   `ApplyEntryOn` (`kv_certPreW_on`/`kv_certPreVW_on` at `kvNxOn γ γk st₀` and the tie, in place of
   `kvCert` and mvcc's `certOk`), `ApplyKVCore` (`srvApplyKVCore_commit` lends `kvBk`'s
   `mvccBackend E.γ 1 B (E.Pk B) ∗ E.BkTie B` and `srvWT E`: `KV.Commit.contract`'s), `StartOn`,
   `apply.UberAdmLBase` (if the last build's `mvcc.BackendBridge`, another track's, was green). Then:
   `UberOn`, `UberKit`, `ApplyNormalOn` (`:794`: `srvApplyKVOn_ua_rt` over mvcc's `storeRT`),
   `EtcdServer__apply` (`:539`: `srvApplyKV_ua_rt_pool`, now `srvApplyKV_ua_pool`), `KVOutcomeOn`,
   `EtcdServer.applyEntryNormal`, `EtcdServer.apply`, `ApplyAllSnap`, `applyAll` (its commit over
   `KV.Commit.contract`, the decision; `backend.Snapshot` over `mvccImage_snapshot.law`).
   **To decide first (minor, the server's own design): where the apply thread's backend reader
   token lives.** `kvOwnPre` (what `dispatch`/`Apply` take) carries `bkWT B ∗ bkRT B`, and
   `applyConfChange.spec` (restated) takes `bkRT d`; `dispatch` gives a reader token back. The
   write-back token comes from the budget (`srvWT E`, `srvWTPool_take`); the reader token has no
   source in the apply thread's state any more (mvcc's `storeRT` was in the sole writer's
   `writerOwn`). The natural fix: a conjunct `∃ d, ⌜E.BkTie = srvBkTie d⌝ ∗ apply.bkRT d` in
   `srvApplyKV`/`srvApplyKVCore` (one reader slot of the counted stock, `backend.rdStock`, taken at
   `NewServer`, the new backend's at `applySnapshot`), lent to each entry. Borrowing from the pool
   (`rdTok_borrow`) would spend the thread token, which `Apply` needs too.
2. **The auth follow-ups** (step 3): `AuthSrv`, `Results.lean`, `InvBoot` (`auth.authParams d.P` for
   the restated `NewAuthStore.spec`), `apply.LessorDerive` (`isApplyLessor_of_lessorInv` over
   `SnapRO.srvRestOwnH_lens_revoke`'s restated lens), and the trust-boundary specs whose contracts
   `SnapRO` restated (`v3alarm.NewAlarmStore.spec`, `lease.NewLessor.spec`, `lessor.Recover.spec`,
   `EtcdServer.restoreAlarms.spec`: `d : BkRef`, `d.b`).
3. **The boot** (`NewServer`, `NewServerAlloc(On)`, `CmpSupply`, `BootBackend`, `InvBoot`):
   `backendRest_open.law`, `mvccW_alloc.law`, `mvccImage_fresh.law`, `mvccBackendFor_open.law`;
   `envAgree` as restated (above); the stand-in `E₀` from `names_nonempty.law`.
4. **The snapshot path** (`SnapApply*`, `RestorePre(M)`, `SnapSendBranch`, `SnapRecvFacts`,
   `ApplyAllSnap`, `EtcdServer.applySnapshot.spec`): over `KV.Restore.contract` (its `mvccOpen` is the
   apply thread's `cmpOwn`; `srvKVCloser*` are gone), `mvccImage_snapshot.law`, the draft's §3c-§3d.
   The `M2*Draft*` modules (mvcc-internal drafts) are to delete or redo.
5. **The request path's proofs** (`EtcdServer__Range`, `__Txn`, `__Put`, `__DeleteRange`,
   `__Compact`, `__newHeader`, `__raftRequest`, `__processInternalRaftRequestOnce`, `__LeaseLeases`,
   `__Authenticate`, `ReadServer`, `LeaseCheck`, `ProposeOn`): their statements' floor is
   `kvLogLb E.γs F` (Range, Txn, Put, DeleteRange, raftRequest, processInternalRaftRequestOnce,
   Authenticate restated); still to restate: `Compact` (`storeReaderC` → `threadTok`, the draft),
   `newHeader` (`storeReader` → `threadTok`, post `newHeaderPostA`), `LeaseLeases` (`storeReader`
   → `threadTok`). The proofs follow `readWit_fire`/`readServed_logR` (restated) and
   `KVStoreRead`'s `srvRdCallA`.

## For the parallel tracks

- v3rpc: `srvApi.histLb` (= `histLbG (kvNx γr on)`), `srvApi.kvPeek.law` (proved: `kvPeek_holds`),
  `srvApi.histLb_model.law` (stated, not proved: it needs the KV invariant's claims),
  `srvApi.srvKVInvsA` with the tie `E.kv = wsIfaceA wsl`; all in `KVStoreApi.lean`. Until the
  server's foundations build, the generic forms in `KVStoreCore.lean` (which builds) are the ones a
  proof can import: `kvPeekG`, `histLbG`, `histLb_bootG`.
- `AEnvA` (§4) is the draft's separate structure for now; the plan is to restate `apply.AEnv` in
  place with its fields (next step) and make `AEnvA` an alias.

## Left (in order)

1. (Done for the definitions, above; the frontier below them is next.) **The apply chain's foundations** (`apply/Chain.lean`, `apply/Contracts.lean`): `apply.AEnv`,
   `kvOwn`, `cmpOwn`, `mPre`, `certPre`, `leasesLive` restated in place as the draft's `AEnvA`,
   `kvOwnA`, ... (`threadTok` beside `kvOwn` in the chain's triples; `putPre`/`deletePre` without
   `storeWT`; the floors `kvLogLb`; `revokeRes` over `rdOwn`/`mvccDeleter`); the components'
   contracts (`isApplyKV` → `isMvcc ∗ ⌜kv = E.kv⌝ ∗ envAus E`; `isAuthStore`, `isAlarmStore`,
   `isCluster`, `isApplyLessor` at `E.Pk B` of the current backend, without mvcc's `storeWT`/
   `storeRT`: not drafted, "by reference"). This unblocks `InvRequest`, `InvImage`, `ServerOn`
   and so `KVStoreApi`.
2. The apply chain's proofs, `applyAll`; `lease.Revoke`'s proof over `mvccDeleter`,
   `Txn.DeleteRange`, `mvccTxn_leaseDelete.law` and `Txn.End` (blocked: see "Found").
3. The boot (`mvccW_alloc.law` now gives `mvccWReg gx ∗ mvccW gx`), the receipts for client/v3's
   `kvLogOk` (`logOk_of_receipt`, proved in `KVStoreApi.lean`).
4. The snapshot send and receive (`senderImage.law`, `dbImageA_open.law`, `restoreArgs.law`, stated).

### Why the server's foundations are red, and what step 1 needs decided

Every server module imports `apply.Chain` (through `wait.Defs`/`apply.Base`, `apply.InvUber`,
`InvRequest`), and `apply.Chain`/`apply.Contracts` name txn's deleted sole-writer API
(`txn.kvWriter`, `txn/Writer.lean`, which no longer builds) and mvcc's internals (`mvcc.storeReader`,
`writerOwn`, `idxCert`, `certOk`, `crevPermAt`, `kbCmpM E.γ.kb`, `storeWT`/`storeRT`,
`csContract … (f : val)`). So nothing above `apply.Chain` builds until step 1 is done, which is
why `KVStoreApi`/`KVStoreLaws` are unbuilt and the builders were proved generically in
`KVStoreCore`. The draft settles `AEnv`/`kvOwn`/`cmpOwn`/`mPre`/`certPre` (its `AEnvA` ... ,
restate in place). Not drafted, to decide before step 1 (all "by reference" in
`clients-server.md`):
- the components' write budget: `isAuthStore`, `isAlarmStore`, `isCluster`, `isApplyLessor`'s
  writing clauses take mvcc's `storeWT γ`/`storeRT γ`, which are the current backend's
  `backend.wbTok`/`rdTok`; over the API they would take those of the backend `B` the clause writes
  (`∀ B, E.BkTie B -∗ … wbTok B.γB …`?), with `csContractA (E.Pk B) E.f`; the draft only says
  "move to `E.Pk B` at the current backend";
- `txnPre`'s `txn.TxnPre log t` (deleted by the txn track: its premise is now `OpsOk`-like);
- `cmpTriple`'s premise (see "Found": `1 ≤ rev`), `cmpPermRq` over `E.Cp`;
- `revokeClause` over the restated `lessor.Revoke.spec` (blocked, "Found").

## Placeholders

None in the proved modules (both of the third session's discharged, "Decisions (2026-11-06)").
No axiom.

## Decisions (the coordinator, 2026-11-06)

- **Finding (2), Revoke, applied (fourth session):** `lease.lessor.Revoke.spec` and `revokeClause`
  take the begin update only for a live lease, `(if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ σ₀
  dels Y) else iprop(True))`, and the not-live arm does not give it back. `applierV3backend.LeaseRevoke`
  builds the pair `(if … then update else True) ∗ (if … then True else wSt E.γs log c)` by cases on
  `id ∈ L`, so the not-live arm keeps the writer's half: no `sorry`. Recorded in the draft
  (`ServerSpecs.lean` §5's docstring and header, `clients-server.md`'s "Superseded (2026-11-06)").
- **Finding (1), txn's `specSole`:** its write wand takes `⌜txn.PathsIgnOk (stateAfter log)
  (t.branch (txnOk (stateAfter log) t))⌝ -∗ Qr σ -∗ …` (the txn track's `ffa7dc68fb`);
  `applierV3backend.Txn`'s wand takes the fact (`iintro %σ %hig …`) and builds the end update with
  `certPre`'s witness: no `sorry`. (`EtcdServer__Txn.lean` calls only the read-only `hTxn.2` and
  is not migrated yet: no write wand there.)

## Found (third session, 2026-11-05; both decided 2026-11-06, above)

1. **`txn.Txn.specSole` (frozen, txn's) is too weak for the apply thread's caller.** Its write wand
   `(if txn.txnReadonly t then True else ∀ σ, Qr σ -∗ txn.txnBeginAU γ log t Qw)` is given before
   the call and not told that `checkTxn` passed. The server builds `txnBeginAU` from its end builder,
   which needs the witness `E.Nx (commitLog log (txnChs log t))`; `certPre` gives it only for a
   `backendStep` outcome, whose applied arm needs `txn.PathsIgnOk (stateAfter log) (t.branch
   (txnOk (stateAfter log) t))`. When the paths miss a previous key-value the request is rejected
   and `commitLog log (txnChs log t)` is no applied log: no witness, no wand. (Until M1 txn's spec
   took `⌜PathsIgnOk …⌝ -∗ certOkNext …` for the same reason.) **Minimal fix** (txn's spec): the
   wand takes the fact, `∀ σ, Qr σ -∗ ⌜txn.PathsIgnOk (stateAfter log) (t.branch (txnOk
   (stateAfter log) t))⌝ -∗ txn.txnBeginAU γ log t Qw` (true where txn calls it: after `checkTxn`'s
   success, whose post states `PathsIgnOk`).
2. **`lease.lessor.Revoke.spec` (the draft's `specA`, as decided) and `revokeClause` are too weak in
   the not-live arm.** The precondition takes `auBegin γ σ₀ (auEnd γ σ₀ dels Y)` always, the
   not-live arm gives it back unused. The server can build that update only from its writer's half
   (`envAus`' begin builder puts `wSt` in the update's private state), and no law recovers it from
   an unused update (an atomic update's private state is hidden): after a not-live revocation the
   apply thread has lost its half of the store's state. **Minimal fix** (the draft and
   `revokeClause`, as txn's `Put` does for a lease): `(if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ
   σ₀ dels Y) else iprop(True))` in the precondition, and the not-live arm without it (the code
   returns `ErrLeaseNotFound` before calling `rd()`, `lessor.go`'s `Revoke`). The caller knows `L`
   (`leasesLive`).

## For the parallel tracks (fifth session, 2026-11-06)

- **`ReadOn` builds** (`726ac24773`), and with it `EtcdServer.Range.spec`, `ReqOn`, `ServerOn`;
  `EtcdServer.{Txn, Put, DeleteRange}.spec` build (`cfa6a13f50`). The read side imports
  `ServerOnDefs`, not the built part.
- Restated names a client sees (old → new):
  - `srvKVCoreM_fire on E γr γ hst L Q : srvKVCoreM on E γr -∗ E.Nx L -∗ □ AU … ={⊤}=∗ ∃ C, …`
    (was: `hlog`, `idxSealed [[],[]]`, `idxSealed L`, `certOk E.γ L`);
  - `srvKVCoreM_keys on E γr l : srvKVCoreM on E γr -∗ E.Nx l ={⊤}=∗ ⌜LogPutsLe etcdKeyMax l⌝`
    (was: a sealed floor `B` and `certOk`); `readM_keys`/`read_keys`: `isServerRead… -∗ E.Nx l`;
  - `srvKVCoreM_cperm` deleted; `srvKVInvs` has a last conjunct `⌜E.Nx = kvNxOff γr.raft γr.kv⌝`,
    `srvKVInvsOn` `⌜E.Nx = kvNxOn γr.raft γr.kv st₀⌝` (patterns ending `%h⟩` need `, -⟩`);
  - `readWit_fire`/`readWit_fireOn` take `E.Nx l` (was `certOk E.γ l`); `readServed_logR(M)`,
    `readIndexOk_logRM` over `kvLogLb E.γs`;
  - `envAgree` is `E.γs = E'.γs ∧ E.Nx = E'.Nx ∧ E.γrev = E'.γrev ∧ E.cmp = E'.cmp`;
    `envAgree_mode`/`_off`/`_on` deleted (no store mode);
  - `srvKVCloser`, `srvKVCloserW` deleted (`Restore` takes `mvccOpen`, in `cmpOwn`).
- Callers outside this track that these break (not fixed): client/v3's `InvWatch`
  (`srvKVCoreM_cperm`, `srvKVCoreM_keys`), `watcher__Watch`, `WatchFire`, `WatchLawsHist`
  (`srvKVCoreM_fire`/`_keys`), `ServedOn` (`readM_keys`), `Results`, `InvServerKV` (`srvKVInvs`'s
  patterns); v3rpc's `ClientModel`, `WatchApi` (`srvKVCoreM_keys`), `Results` (`read_keys`),
  `ServerKVOn` (`rangeReadOkM`/`txnReadOkM`); the examples' `compactkv/NoDup`, `cachekv/NoDup`
  (`srvKVCoreM_fire`), `compactkv/Main` (`srvKVInvs`), `watchkv/Main`, `authkv/Main`,
  `linkv3p/startCluster` (`envAgree_off`); `etcdserver/Link.lean` (generated: the restated specs'
  hypotheses).

## For the parallel tracks (fourth session, 2026-11-06)

- **`InvRead` builds** (`a25b814824`), with `KVApplyOn`, `InvApRes`, `apply.AuthFuel`,
  `apply.AuthApplyLatest`, `AuthApplyRes` and `KVStoreRead`; then `apply.AuthStepsX`,
  `apply.AuthApplyLatestPut` (`18f9b6c5a5`), `AuthGuard`, `AuthBound`, `AuthReqDerive`
  (`f96caecb2f`).
- **`ReadOn`'s remaining blockers** (red, next on v3rpc's path):
  - `KVRead`: `readServed_logR` is mechanical (`idxCert` → `kvLogLb`, as `readIndexOk_logR`);
    `readWit_fire` takes `mvcc.certOk E.γ l` and goes through `KVLemmas.kv_read_log` (still over
    mvcc's `certOk`, with the removed tie `E.γ.cok = γr.kv.cok`). Over the API its certificate is
    `E.Nx l`, and `kv_read_log` needs restating over `kvNxOff γr.raft γr.kv l` (`= kvNx γr false`),
    which needs the tie `E.Nx = kvNxOff …`. `srvKVInvs` dropped that tie (step 1: it names the KV
    model, above `InvApplier`). To decide: carry it in `srvEnvOk`/`isServerRead` as a pure
    `E.Nx = kvNx γr on`, or restate `readWit_fire` at `kvNxOff`, with its callers passing the tie.
  - `InvApplyAll`: `E.P`, `MvccName.withPhys`/`phys` (the old physical-backend renaming), `:72`'s
    type.
  - `apply.AdminChain:199`: `chainRes c.quota …` no longer gives the wand it expects
    (the chain's restated `mPre`).
- Callers outside this track that the restatements break (not fixed here): `Link.lean`s generated by
  `etc/gen-link.py` (`etcdserver/Link.lean`, `client/v3/Link.lean`: `lessor.Revoke.wp_proof`'s new
  hypotheses `hBT hsh hisB hLD` in place of `hDel hEnd`); `client/v3/lessor__Revoke.lean`; the users
  of `InvRead`'s restated read path and of the deleted `storeSmall*`: v3rpc's `ServerKV`,
  `ServerKVOn`, `ClientModel`, `Results`; client/v3's `InvServerKV`, `ServerKVGet`, `ServerKVPut`,
  `ServerKVTxn`, `ServerWatcher`, `InvWatch`, `ServedOn`, `ServeFromStart(On)`, `Results`; txn's
  `ClientLaws`; mvcc's `InvCompact`; the examples' `common/{Defs,Served,ServedLease,Serve}`,
  `watchkv`, `linkv3p`, `restart3`, `cachekv`, `compactkv`.

## For the parallel tracks (second session)

- Callers outside this track that break on step 1's restatements: `client/v3/InvServerKV.lean`
  (`kv_cert_floor`'s new signature), the `Results.lean`/`AuthSrv`/`ApplyNormalOn` users of
  `isAuthSteps_of_authInv` (new `hf`), `srvEnvOk_kbCmp`'s three users.

## Decisions (the coordinator, 2026-11-05)

- `lessor.Revoke.spec` takes `⌜MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63⌝` (applied,
  `Spec/.../lease/lessor__Revoke.lean`; the draft and `clients-server.md` record it superseded).
- `applierV3backend.Compaction.spec` takes `⌜1 ≤ sint.Z rev⌝` (lands with the chain's
  restatement; the draft records it).
- The components' contracts (auth, alarm, cluster, lessor) take the current backend `B`'s
  `backend.wbTok B.γB` / `backend.rdTok B.γB B.P B.b ∗ backend.bOpen B.γB backend.rdOpen` in place
  of mvcc's `storeWT γ` / `storeRT γ` (which were exactly those of `γ`'s backend).
- `txnPre` and `cmpTriple`'s premise follow txn's restated specs as landed in
  `Spec/.../etcdserver/txn/`, else `notes/mvcc-api-clients/TxnSpecs.lean`.

## Found (second session, 2026-11-05; not decided: Revoke's proof stopped)

- **`lease.lessor.Revoke.spec` (as fixed) is unprovable over the frozen API: no backend fact for
  `le.b.BatchTx()`.** After the deletes, `Revoke` runs `schema.UnsafeDeleteLease(le.b.BatchTx(),
  …)`. `mvccTxn_leaseDelete.law` gives the WP of `UnsafeDelete` on the backend's batch transaction
  `t` from `backend.bF go!"batchTx" B.b ↦□ t` (its premise), which only `backend.backend.BatchTx.spec`
  gives, and that spec takes `backend.isBackend B.γB B.P W Pk' B.b` (some `W`, `Pk'`). Revoke's
  precondition has `mvccBackend γ q B P` (sealed: its `□ isBackend … (mvccW gx) P B.b` is hidden),
  `hookIs B f`, `lessorBeOn lp B.b` (only `le.b`'s field) and nothing else of `B`; no API law
  exposes `isBackend` from `mvccBackend`. (The old proof took `BatchTx`'s triple from mvcc's
  internal `bkBt`, inside the write transaction's facts.) **Minimal fix**, either:
  (a) an API law `mvccBackend_isBackend.law : ∀ γ q B Pk, mvccBackend γ q B Pk ⊢
      ∃ gx, □ backend.isBackend B.γB B.P (mvccW gx) Pk B.b` (true by `mvccBackend`'s body; the
      server's other readers of `s.be` would use it too), or
  (b) Revoke's precondition takes `□ backend.isBackend B.γB B.P W Pk' B.b` for some `W Pk'`
      (both callers have one: the server's `srvBeRO B`, the tester's `backend.New`).
  (a) is the API's; (b) a client-spec change. The Revoke proof is stopped until decided.

## Found (both decided above)

- **`lessor.Revoke.specA` (landed as drafted) is unprovable over the frozen API: it lacks the
  begin state's reachability.** The proof must show that the loop's `Txn.DeleteRange(key, nil)`
  calls, one per key of the lease's item set (`l.Keys()`, sorted), leave exactly `dels =
  leaseDels (stateAfter σ₀.log) id` pending, since `End`'s update (`mvccTxn_leaseDelete.law`'s
  triple, `Txn.End.contract`) commits `σ.notify pend` for the transaction's actual `pend` and the
  caller's `auEnd γ σ₀ dels Y` takes `σ.notify dels`. Each call deletes
  `delKeys σ₀.log pend true k []` (mvcc's index answer), which is `[k]` for a key of the state
  only under `LogOk (σ₀.log ++ [pend])` and `σ₀.log ≠ []` (`txn.delKeys_eq`), i.e. `σ₀`'s log well
  formed (`LogWf`, from `MvccReachable σ₀` by `reach_logWf`). The precondition gives only
  `σ₀.pending = none ∧ (stateAfter σ₀.log).length ≤ 2 ^ 62`; the only API fact of reachability is
  `mvccState_reachable.law`, which needs `isMvcc kv γ`, not in the precondition (`mvccDeleter rd γ`
  has none), and the deleter's begin update gives the proof no access to the state. (True of every
  run, since the begin update commits only at mvcc's real, reachable state; not provable from what
  the API exports.) **Minimal fix**: add `MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63` (txn's
  `Reach σ₀`) to the pure premise. Both callers have it: the server's apply thread from the
  writer's facts (`kvAus.law`'s last conjunct gives exactly `MvccReachable (stAt log c) ∧ log.length
  + 3 ≤ 2 ^ 63`), the tester from `mvccState_reachable.law` on the state it holds. (Alternatively
  `mvccDeleter`'s triple could return the begin state's reachability with `R σ`.) The Revoke proof
  is stopped until the user decides.

- **`applierV3backend.Compaction.specA` is unprovable over the frozen `KV.Compact.contract`**
  (not landed). The draft's precondition is `⌜sint.Z rev < log.length⌝ ∗ E.Cp (sint.Z rev)` with
  `E.Cp = crevOk γr`, and `crevOk γr (-1)` holds (`⌜c = -1⌝` is its first disjunct), so the spec
  admits `rev = -1`; but `KV.Compact.contract` takes `⌜1 ≤ sint.Z rev⌝` (added 2026-11-04,
  `04dd363d79`, after the draft froze), so `Compaction`'s call of `KV.Compact` cannot be proved at
  `rev = -1` (nor at `0`, which `crevOk` excludes). Minimal fix: the premise
  `⌜1 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝` (its caller has it: a compaction request's revision
  is positive, `EtcdServer.Compact.spec` requires it); alternatively `E.Cp` the cluster permit
  `kvCmpPermit γr.kv` (positive) rather than `crevOk`.
