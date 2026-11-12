# Track SV of the `origin/lean` → `mvcc-api` merge (2026-11-06)

Scope: etcdserver outside `apply/`, `txn/`, `api/` and the snapshot files (38 conflicted files). All
resolved, no markers left, all `git add`ed. Nothing built (no `lake build`, no `lean-check`).

Conventions used throughout (stated once):
- **Receipts and lease answers.** `resultIsW`, `resultIsWOn`, `resPostM`, `appliedOkM`: this branch's
  conjuncts (`kvLogLb`, `E.Nx`, then `⧖ (logCh …) ∗ ⌜LogWf' ∧ +3⌝`) first, `lean`'s
  `grantArM ∗ revokeArM` (`grantAnsM ∗ revokeAnsM`) **appended last**. Every pattern in my files follows.
- **New conjuncts of the KV invariants appended last**: `srvKVInvs` gets `lean`'s `⌜γr.kv.lm = E.lm⌝`
  as a 7th conjunct after `⌜E.Nx = kvNxOff …⌝`; `srvKVInvsOn` gets `⌜γr.kv.lg = false⌝` after
  `⌜E.Nx = kvNxOn …⌝`. Patterns of other files that stop at `%HNx⟩` need one more `-`.
- **`lease.rdAt E.γ.leases E.s`** → `(∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗
  mvcc.api.mvccDeleter rd E.γ)` (inline, as the snapshot track's `SnapApplyDefs`).
- **`WTNames`** (`lean`'s `srvWTPool E (W : WTNames)`, H2's monitor register) kept, with this
  branch's `bkKey d`, `apply.bkRT d`, `srvWT E`, `E.BkTie = srvBkTie d`.
- **Auth-on snapshot plan** (`T : auth.AuthBkNames`, `adminWC`, `authWHeld`, `latestResC`, the row on
  the backend `d`) kept, at this branch's one batch-lock invariant `Pk` (`E.Pk = fun _ => Pk`) and
  `f : GoFunc` (in place of `E.P`, `f : val`).

## Per file

- `AdminOn`, `AuthnOn`: patterns `#Hspc` (ours, `spanCtxOk`) + `lean`'s `hRR` rewrite (spec folding).
- `AdminEntryOn`: `adminEntryOn.spec` binders `(T : auth.AuthBkNames) (Pk : IProp GF)`; `adminWC stl bel
  γa Pk E.f T`, `authWHeld γa T`, `authWBackendAt … Pk E.f (authWTok T)`; proof: `lean`'s
  `authWHeld` unfolding + ours' `kvOwnPre` building, `ownFuT_lendC … Pk`.
- `AppliedOn`: `lean`'s new `applied_jumpM` kept with `mvcc.idxCert E.γ.idx L` → `srvApi.kvLogLb E.γs L`;
  `appliedLogAt_kvLogAtM` dropped here (ours moved it to `ServerOnDefs`); `srvApplyKVOn`'s `rdAt` restated.
- `ApplyCmpArm`: ours (`cmpAdmit` without the store mode). `revokeOwn_take`'s `rdAt` restated.
  **MERGE-TODO(lease)** on `lean`'s `kv_certPre_G` (over `E.γ.cok`).
- `ApplyNormalOn`: `srvAuthApplyResB_open`, `srvAuthApplyResB_publish`, `srv_uberAuthStepsL_at`
  rewritten as the combination (auth-on snapshot + `Pk`); its `srvWTPool_take_n` at `γp.cnt`/`srvWT E`.
- `AuthApplyRes`: `(f : GoFunc) (T : auth.AuthBkNames)`.
- `BuildGap`, `StartOn`: ours' KV row + `lean`'s `#Hrvkb` (revoke-open); `StartOn`'s `rdAt` restated.
- `BuildLemmas`: ours (F2's ties dropped: `isBackend_withCm` etc. without `t`). `lean`'s
  `srvStopChans_boot` re-added at ours' instance (`mvcc.lateW d.gx`), **MERGE-TODO(close)**.
- `EtcdServer__Txn` (proof): `lean`'s (rewritten read path) + ours' `Tracer.Start` pattern (`#Hsp, -`).
  Its body is still over mvcc internals (`storeReader`, `idxCert`, `certOk`, `hTxn … E.s`):
  migration is next-phase work (it was not migrated on this branch either).
- `EtcdServer__apply`: ours' `srvApplyKV_small` (laws, `Hkvi`) at `lean`'s `entryOk E.lm`.
- `EtcdServer__applyAll` (proof): `lean`'s (AuthC component) + ours' laws (`hsh hPers hReach hImg` for
  `hC`), the snapshot's `threadTok` lent from `srvGoRes`, `hRB` for `applyEntries`, the merged window
  over the API. **MERGE-TODO(window)**: `lean`'s component arguments to `mergedCreate_window`.
- `EtcdServer__applyEntryNormal`: 19 hunks combined: ours' writer facts, tokens (`srvBeOwn_pool`,
  `bkToks_srv`, `threadTok`) + `lean`'s lease-expiry (`revokeOwn_take`, `srvRest_open`, `HLt HEv Hrv`,
  `U`, `srvRest_applyP*`, `grantReqA_*`), `rqOk_of_false`, `restLeasesWith_mem`; `trig'` dropped
  (`lean`). **MERGE-TODO(apply)** ×2 (the order of the merged `apply.Apply.spec` pattern) and
  **MERGE-TODO(lease)** ×2 (`kv_certPre_M` called at `E.lm`, `Hnl`, `kvTableOf_ne0`).
- `EtcdServer__processInternalRaftRequestOnce`, `EtcdServer__raftRequest`: `lean`'s one-spec proofs +
  ours' `#Hspc` and receipts; patterns at the convention above.
- `EtcdServer__run`: `lean`'s throughout. **MERGE-TODO(receipts)** on `run_job_body`: `specBatch` now
  takes `receiptBound GF ≤ 2 ^ 48` in both modes, `run` carries `acReceiptOk K`.
- `InvApplier`: `srvKVInvs` (convention), `srvEnvOk` ours + `srvRestOwnH E.authMode`
  (`srvEnvOk_kbCmp/_cm/_off` dropped), `srvBeHooked`/`srvBeRO` ours (`mvccW gx`),
  `CmpTies`'s `Inhabited` dropped, `srvWTPool` (convention), `srvWTPool_alloc` `lean`'s at
  `E.BkTie`, `wbSupply_of_stock` (ours, at `WTNames`), takes at `γp.cnt`; `srvApplyKV`'s `rdAt` restated.
- `InvApplyAll`: `srvWTPool_beSucc` at `WTNames`.
- `InvBuild`: `srvC_agree` is `lean`'s `rfl` (the contract reads no name of `E`); `rdAt` restated.
- `InvRequest`: `resultIsW` (convention). `InvRun`: `lean`'s (split, `InvRunRes`) + the KV row.
- `InvWatchBuilt`: `lean`'s `srvWatchReaders`, `srvWatchReaders_storeReaders` kept, **MERGE-TODO(close)**.
- `KVApply`: `kvEntry_len` at `{lm}`, `entryOk lm`, ours' `+3` bound; `kv_applied_step` `Hlg` the 7th conjunct.
- `KVApplyOn`: `lean`'s `kvRaftOfOn_length_le` kept, `kvRaftOfOn_extends` dropped (ours moved it to
  `KVAuthModel`); `srvKVInvsOn` (convention), #7-on's `E.cmp = false` **dropped**.
- `ModeSpecs`: `lean`'s (folded) + ours: trace import, `srvWT E`, `receiptBound` premise in
  `apply.specOff`/`applyEntries.specOff`, `spanCtxOk`+`kvLogLb` in the two request `specOff`s, their
  `spec_off` proofs' patterns.
- `ReadOn`: ours' pattern + one `-`. `ReqOn`: convention.
- `ServerOn`: imports both (`ServerOnDefs`, `ImageOn`); the moved sections stay out (ours'); `srvCM_agree`
  `lean`'s `rfl`, `rnTickerOk_srvErM_S` dropped (`lean`); `applyBuiltNAOn`'s `rdAt` restated.
- `StoreLatest`: `authApplyResB` on `d : KBReal`, `Pk`, `f : GoFunc`, `T : AuthBkNames`;
  `srvAuthApplyResB` `∃ stl d Pk, ⌜E.BkTie = (fun B => iprop(⌜B = d⌝)) ∧ E.Pk = fun _ => Pk⌝ ∗ …`;
  `lean`'s `adminWC`, `authStepsAny`, `ownFuT_lendC`, `authApplyResB_kb_congr` at `f : GoFunc`.
- `UberOn`: as `StoreLatest` (proof rewritten as the combination).
- Spec files: `apply`, `applyEntries` (`WTNames`, `logShapeM … E.lm`, ours' unconditional
  `receiptBound`); `applyConfChange` (`srvRestOwnH E.authMode`, `E.BkTie`); `setAppliedIndex`
  (`lean`'s `rep` replay case, `kvLogLb`); `Txn` (`lean`'s folded spec, `kvLogLb`); `applyAll`
  (`lean`'s, the KV row over `isMvcc`, `receiptBound GF ≤ 2 ^ 48` in place of `acReceiptOk C`);
  `NewServer` (`lean`'s `specG` + ours' four store premises; **MERGE-TODO(close)** on `srvWatchReaders`).

## Spec changes (client specs; old → new)

- `EtcdServer.applyAll.specBatch`: pure premise `acReceiptOk C` → `receiptBound GF ≤ 2 ^ 48` (both modes).
- `EtcdServer.apply.spec`, `applyEntries.spec`, `apply.specOff`, `applyEntries.specOff`:
  `(E.authOn = true → receiptBound GF ≤ 2 ^ 48)` → `receiptBound GF ≤ 2 ^ 48` (ours').
- `srvKVInvs`: + last conjunct `⌜γr.kv.lm = E.lm⌝`; `srvKVInvsOn`: + last `⌜γr.kv.lg = false⌝`,
  without #7-on's `E.cmp = false`.
- `resultIsW`/`resultIsWOn`/`resPostM`/`appliedOkM`: `lean`'s grant/revoke answers after ours' receipts.
- `srvAuthApplyResB`, `adminEntryOn.spec`, `srvUberOn`-family: `Pk` with `lean`'s `T : AuthBkNames`.
- Everything else: as either side had it.

## Not done here (outside my list; each breaks against my resolution)

- `KVModelM.lean` (ours): `srvAuthSt0` now also in `lean`'s `ImageOn.lean` (both imported by
  `ServerOn`: a clash; delete ours'); `logShapeM` needs `lean`'s `(lm : lease.Mode)` and its lemmas.
- `ServerOnDefs.lean` (ours): needs `lean`'s changes to the moved `uber` section: `srvUberOn`'s
  `∀ γc`, `latestResC`, `T : AuthBkNames`, `adminWC … (authWTok T)`, `srvUberOn_kv γc`,
  `srvUberOn_adm` (at ours' `Pk`).
- `InvRunRes.lean` (`lean`'s split of `InvRun`): line 272 `txn.isKV kv B.E.s B.E.γ` → `□ isMvcc kv B.E.γ ∗ ⌜kv = B.E.kv⌝` (ours' change, moved there).
- `ApplyAllSnapOn.lean`: `applied_jumpM`'s `idxCert` argument → `kvLogLb`.
- `apply.Apply.spec` (apply track): the order of its merged post (`MERGE-TODO(apply)`).
- `mergedCreate_window` (snapshot track): its merged statement (`MERGE-TODO(window)`).

## Non-conflicted etcdserver files (outside apply/txn/api/snapshot) over removed mvcc internals

Comment-only hits omitted (InvRead, InvRest, InvServe, KVStoreApi/Core/Read, LeaseGrant, WorkloadDefs,
ApplyEntryOn, specs of Compact and applySnapshot).
- `AuthCompRows`: `rdAt` in `srvApplyKVC` rows (restate as above); `srvApplyKVC_idxCert` → the writer facts (`applyKV_writer`).
- `CompactEnv`: `mvcc.storeReaderC E.s E.γ`, `idxCert_len` → a thread token / `kvLogLb` (the Compact request path).
- `CompactMode`: `idxCert ∗ certOk` predicate → `kvLogLb ∗ E.Nx` (or delete if unused).
- `EtcdServer__Compact` (and spec comment): `idxCert_nil` → `monoListLbOwn_nil`'s `kvLogLb E.γs []`.
- `EtcdServer__LeaseGrant`, `EtcdServer__LeaseRevoke`, `EtcdServer__newHeader`: `idxCert_nil` → `kvLogLb E.γs []`.
- `EtcdServer__Range`: the read path over `storeReader`, `idxCert`, `certOk` (as `Txn`'s; migrate with `KVStoreRead`).
- `EtcdServer__Cleanup` (proof and spec): `mvcc.wsCloseRes … ={⊤}=∗ bOpen d.γB 1` — **close decision**.
- `StopApi`, `StopReaders`, `StopShutdown`, `StopImage`, `InvRestart`: `storeReader` census, `srvKeepRdN`,
  `wsCloseRes`, `stop_census`, `lateWD`/`KBReal.snap` — **close decision** (risk 1).
- `InvBoot`, `NewServer`: `newPostK … mvcc.lateWB`, `storeReader` replicas (64), `isBackend_withCm … tt`,
  `srvStopChans_boot … tt` (now without the ties) — the boot over `mvcc.api.New.spec` (not started) and close.
- `InvStart`: `rdAt` in `start`'s row (restate as above).
- `KVLemmas`, `KVReadOn`: `kv_cert_read`/`…On` over `mvcc.certOk` (ours' known leftovers; delete when unused).
- `ProposerLemmas`: `mvcc.idxCert E.γ.idx F` → `kvLogLb E.γs F`.
- `Results`: `idxCert` in restated results' statements (`processInternalRaftRequestOnce`/`raftRequest`
  results) → `kvLogLb`; plus `applyAll.wp_proof*`'s new arguments.
- `CmpSupply`, `RunOn`, `AuthBkHook`, `EtcdServer__applyConfChange`, `Spec/EtcdServer__snapshot`:
  `E.γ.kb`, `kbCmpM`, `mvcc.storeWT`, `txn.isKV` or `lateWD` (grep `E\.γ\.kb|kbCmpM|storeWT|isKV|lateWD`):
  the tie `E.BkTie = srvBkTie d`, `srvWT E`, the `isMvcc` row.

## API weaknesses seen

Only the known one: the census of store readers for `backend.Close` (`srvWatchReaders`,
`storeReader` replicas, `wsCloseRes`) has no API counterpart (risk 1, the user's decision).
