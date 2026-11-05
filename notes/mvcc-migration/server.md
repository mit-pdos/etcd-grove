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
- **Next in step 2**: `uberApplier.dispatch` (770 lines; its spec takes `kvOwnPre v3 …`, the KV
  methods' `mPre` from it by dropping `bkWT`/`bkRT` into the post's `∃ B, bkRT B`, the writing
  methods' `mPreW`/`mPreV` directly; `threadTok` through every triple), `uberApplier.Apply` (its
  lent `A` now `kvOwnPre v3 E x.log Pre Q Post ∗ threadTok ∗ …` in place of `kvOwn ∗ storeWT ∗
  cPre`; `rdLend` of it needs a `kvOwnPre` form of `rdLend_kvOwn`), then `applyAll`. The `Link.lean`
  hypotheses changed: `newHeader` (`shapes` for `mvcc.store.Rev`), `Compaction` (`hTODO`, `hEnsure`,
  `shapes`).
- **The auth track's follow-ups (its `cca7e9a4a9`, `notes/mvcc-migration/auth.md`)**: done in
  `AuthSteps`; not yet in `AuthStepsX` (red below on `AuthFuel`), `StoreLatest`, `AuthApplyRes`
  (`f : val` → `GoFunc`), `AuthSrv`, `Results.lean` (drop `isAuthSteps_of_authInv`'s `hf`),
  `SnapRO.authApplyOk`/`authRecoverOk` and `InvBoot` (over `BkRef`, `auth.authParams`; `InvBoot`
  blocks auth's last two modules).
- **Not started**: step 2's `applyAll`; step 3 (`lease.lessor.Revoke`'s proof: `mvccBackend_isBackend.law`
  landed, `c1f1565c78`; but see Found (2) of the third session, the not-live arm); the boot (step 3:
  `mvccW_alloc`, `mvccImage_fresh`, `mvccBackendFor_open`, and `backendRest_open.law` once mvcc lands
  it); the snapshot (step 4).

**The frontier** (red, next): `InvProposer` (a floor over `idxCert`), `InvApplier` (the old
`srvKVInvs`, `envAgree`'s mode ties, the sole writer: its restatement is the draft's
`srvKVInvsA`), on which `KVModel` → `KVApply` → `KVChainOff` → `KVAuthModel` → `KVModelM` →
`KVStoreApi` wait; `apply/AuthDerive` (partly restated), `AuthLemmas`, `AuthSteps` (proofs over
the old `E.P`, `kvOwn`); the chain's method proofs.

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

- `apply/applierV3backend__Txn.lean`: `-- M1-REPLACE` in the write wand for a request whose paths
  miss a previous key-value (Found, third session, (1); decided: discharged once txn's wand with
  `PathsIgnOk` lands, see "Decisions (2026-11-06)").

No axiom.

## Decisions (the coordinator, 2026-11-06)

- **Finding (2), Revoke, applied (fourth session):** `lease.lessor.Revoke.spec` and `revokeClause`
  take the begin update only for a live lease, `(if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ σ₀
  dels Y) else iprop(True))`, and the not-live arm does not give it back. `applierV3backend.LeaseRevoke`
  builds the pair `(if … then update else True) ∗ (if … then True else wSt E.γs log c)` by cases on
  `id ∈ L`, so the not-live arm keeps the writer's half: no `sorry`. Recorded in the draft
  (`ServerSpecs.lean` §5's docstring and header, `clients-server.md`'s "Superseded (2026-11-06)").
- **Finding (1), txn's `specSole`:** its write wand takes `⌜txn.PathsIgnOk (stateAfter log)
  (t.branch (txnOk (stateAfter log) t))⌝ -∗ Qr σ -∗ …` (the txn track); `applierV3backend.Txn`'s
  wand takes the fact and builds the end update with `certPre`'s witness: no `sorry`.

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
