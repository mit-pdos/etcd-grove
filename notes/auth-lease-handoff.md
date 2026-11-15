# auth-lease handoff (`etcd_authlease_safe`)

Plan: `notes/auth-lease-scope.md` (approved; §0, §2, §5, §7). Decisions Q1–Q9: `questions.md`,
section "auth-lease". Worktree `/shared/etcd-grove-rs56`, branch `auth-lease` (off lean `89ef103d5b`,
with `auth-lease-scope` merged).

## Done

- **S0 (probe), 2026-11-14.** Unlinked, untracked: `Scratch/AuthLeaseProbe.lean` (the apply layer's lease
  check at the latest state) and `Scratch/AuthLeaseProbeModel.lean` (the mode-`on` model on the triple
  state). Both check with no `sorry`. Findings: CP0 report (below, "Pitfalls").

- **S1 (empty-user fix), 2026-11-14** (go from etcd-grove-81): `leaseCheckFrom` over `principalBound`,
  `v3rpc.leaseCheckT` over the new `v3rpc.principalBoundT` (`infoBoundTM` deleted); lemmas
  `principalBoundOn_of_ctxBound`, `principalBound_ctx` (`LeaseCheck.lean`); ledger and decisions.md entries;
  full build passes; interfaces unchanged (`gen-interface --check` on every `etc/api` list); waiting for the
  coordinator's go to run `etc/land.sh`.
- **S2 Draft** (design text): `notes/auth-lease-s2-draft.md`, reviewed in rounds (`/shared/tmp/auth-lease/`).

- S1 landed: lean `28b89b9dd6` (2026-11-14).
- **S2 (apply layer at the latest state with a lessor), proved, 2026-11-15** (Freeze approved by
  etcd-grove-81 with the five design choices): `AuthLatest` (lease vocabulary, `isAuthStoreL`'s snapshot
  clause), `AuthApplyLatestPut` (`checkLeasePuts{,Keys}.specL`, `checkPutAuth.specL`, `Put.specL`),
  `AuthApplyLatestTxn` (`txnPutsW`, `txnOutLL`, the txn checks), `AuthApplyLatestRevoke` (new:
  `revokePreW`, `LeaseRevoke.specL`), `AuthApplyLatest` (`authOutLL`, `kvPostFL` + lease class),
  `DispatchKVL` (`authKVKind`, `kvOutL`/`kvShapedL` with leases, `applierKVL`'s revocation triple,
  `dispatch.kvSpecL` widened, the revocation branch), `ApplyKVL`/`ApplyFnKVL` widened, `UberKVLBase`,
  server: `KVOutcomeOn` (`txnPutsW_plain`, `authOutL_of_kvOutL` over `plainCover`), `ApplyNormalOn`,
  `UberOn`, `UberKit` (`LeaseRevoke.specL`), `EtcdServer__applyEntryNormal`, `Results`
  (`apply_lease_revoke_latest`). Full build green; lean `dd068e790f` merged.

- S2 landed: lean `c3da59fa29` (2026-11-15).

## Next, in order

1. S3, revised (etcd-grove-81, 2026-11-15, option (a) of `/shared/tmp/auth-lease/s3-scope-gap.md`; 26–40 days after
   S3a review r1's F1 (ii), F2 (a), F3),
   in three Freeze packages:
   - **S3a** (now): the model and the apply thread: the triple state with the lease table, the client's half kept in
     `kvInvOn`, the auth-on table for `srvRest`, `authKVKind` in the three places, admission of grants, revocations and
     leased puts at the revocable mode. Design: `notes/auth-lease-s3a-draft.md` (revision 4 = the S3a Freeze package,
     three review rounds `/shared/tmp/auth-lease/s3a-review-r{1,2,3}.md`; N1 (ii′): `leaseExactL` in the class
     track's `kvPostF`); **frozen at revision 5** (etcd-grove-81, 2026-11-15, after round 4; tag
     `auth-lease-s3a-frozen`). **Probe done** (2026-11-15): `kvOwnAt` and `kvOwn ⊣⊢ ∃ L, kvOwnAt E log L` proved
     (`Scratch/S3aProbe.lean`, untracked); `applierV3backend.Put`'s proof has the live set `L` in hand and splits
     on `o.leaseID = 0 ∨ o.leaseID ∈ L` (`applierV3backend__Put.lean:97-170`), rebuilding `kvOwn` at the same `L`
     (`kvOwn_of_split`), so its `kvPostF` conjunct is local; the key-length bound is closed by §5. **Prove: started 2026-11-15, STOPPED at a finding**
     (see "S3a Prove: where it is" below). Order (Draft §8): (1) the model (`KVAuthModel.lean`: `OnState`, `kvEntryOn`/`kvRaftOfOn` on it,
     `kvGrantedL`/`leaseGrantedM`/`leaseOk` from `Scratch/AuthLeaseProbeModel.lean`, `plainEntryOn lm`/`plainReqL`/
     `txnPlainL`, `entryDetOn`/`entryShapeOn lm`, `keysNonEmpty`, `keysLeasesLive`, `KVAuthBridge.leaseOk_iff`);
     (2) `kvInvOn` + alloc, `appliedTableM`, `srvKVInvsOn`'s rows (`lm = E.lm`, `pre = []`), `appliedTableM_eq_model`;
     (3) `kvOwnAt`/`leaseExactL`/`kvPostF`'s conjunct through backend/quota/capped/corrupt/auth, `kvPostFL`, the four
     layer triples; the apply thread's model (`outcomeOn`, `kvAppliedOn`, the S2 `plainCover` lemmas restated);
     (4) the snapshot path (§5, its frozen `hnl` text); (5) `applyEntryNormal.wp_proofOn`/`apply.wp_proofOn`, the
     examples' proofs. `KVAuthModel` rebuilds ~1500 modules: full builds under the flock.
   - **S3b**: the request side (grant, revoke, leased put with auth on).
   - **S3c**: the couplings and `NewServer`; the `lease.bootCfg` hub change and the `NewLessor` docstring (hard stops).
   - The auth-on snapshot path carries the leases (F2 (a)); the latest track gains a lease-exact outcome (F1 (ii)).
2. S4 with the client's leased put (`WithLease`, `Put`/`Txn` with a lease) and linearizable client specs of
   `Lease.Grant`/`Revoke` (F3).

## S3a Prove: where it is (2026-11-15, after rev 6)

Rev 6 (§14) FROZEN with the stronger guard (etcd-grove-81); its frozen-text edits are made (`EtcdServer.{Put,
DeleteRange}.spec`, `txnAppliedOk`, v3rpc `putApplied`/`deleteApplied`/`txnAppliedAns`, client `KVService` rows,
`readQ_of_ansM`, `srvKVCoreM_fire` + `srvKVFacts_fire(0)`, `kvLogOkTo`). The tree does NOT build yet.

**Strategy: a transitional port first.** `srvKVInvsOn` keeps a TRANSITIONAL `γr.kv.lg = false` (beside the frozen
`lm = E.lm ∧ pre = []`); the apply and snapshot proofs take `lm = none` from it (`KVNames.lm_of_lg_false
Hrows.2.2.1`, marked "TRANSITIONAL until the §5 step") and keep their `plainCover` reasoning. Steps 3 (§3a
`leaseExactL`/`kvOwnAt`/Chain's `kvPostF`), 4 (§5, drop the transitional row) and 5 (revocable-mode apply arms) come
after the tree builds.

Checked clean with `etc/lean-check.py` (in order): KVAuthModel, KVApplyOn, KVModelM, KVReadOn, KVAuthShape, ProposeOn,
ServerOnDefs, ImageOn, ServerOn, NewServerAllocOn, AuthTie, AuthTieRead, ReqOn, ReadOn, auth/Hist, KVOutcomeOn,
ApplyEntryOn, ApplyTieOn, ApplyNormalOn, SnapRecvOn, MergedImageOn, SnapAuthRecover, AuthCompRows,
Spec/EtcdServer__applyAll, ApplyAllSnap, ModeSpecs, EtcdServer__Range, EtcdServer__apply, EtcdServer__applyEntryNormal,
StartOn, RunOn, NewServer, EtcdServer__applySnapshot (SnapApplyPost), SnapSendBranch, StopShutdown, EtcdServer__run,
ClientModel, EtcdServer__Put/DeleteRange/Txn. Edited, not yet checked: auth/MainAlloc, etcdstart/Alloc3On (alloc premises),
server Results (`server_member_alloc_on` premises), KVLogOk, client WatchFire/Results/KVService, v3rpc ServerKV, InvRead.

**Where it is (2026-11-15, session 2):** the full build is GREEN at `build9` (`/shared/tmp/auth-lease-s3a/build9.log`,
flock + 64G, commit after `auth-lease S3a §3a`); `etc/tcb-report.py --check` at 870 axioms, 4 sorries (run at `build8`,
before §3a; §3a adds no axiom). Done this session:
1. **The read rows' guard** (handoff item 1, decided by etcd-grove-81): `⌜on = true → γr.kv.lm = .none → kvLeasesOn γr.kv
   srvAuthSt0 L = []⌝` inside the `∃ L` of `rangeAnsOkM`/`txnReadAnsM` (`ServerKV.lean`), proved in `ServerKVOn` by
   `ReadOn.depQ_leases_none` (from `srvKVCoreM_leases_none`: `kv_log_plain_on` + `kvLeasesOn_none`; `iapply wp_fupd` before
   the `wp_apply` so the post can be updated). `readQ_of_ansM` (client Results) takes the guard;
   `rangeErrReply_of_errAt` became a fupd lemma over `srvKVCoreM E.authOn` (the error row `rangeErrAt` keeps its text).
   §14's table has the two rows.
2. **Client chain and examples** destructure the table (`ServerKVGet`, `ServerKVTxn`, `ClientPutGet`, `kubernetes/Defs`,
   k8s `etcd3/Compact`, `partition/WatchWrites`, `txnlin/Calls`, `auth/WorkCalls`). Pitfall: `simp only [hs, …]` on an
   Iris goal rewrites the context too: specialize `Himp $$ %hs` BEFORE the simp.
3. **§3a**: `apply.leaseExactL`, `leaseExactL_rejected`, `leaseExactL_other`, `kvOwnAt`, `kvOwn_iff_at`, `kvOwn_of_at(P)`,
   `kvOwn_atP`, `kvOwn_rejected`, `kvOwnAt_ltHalf` (Chain); `kvOwnAt_of_split`, `wSt_ne_false` (WriteLemmas). `kvPostF` and
   `kvPostFL` carry `∃ L, ⌜leaseExactL L rq log oc⌝ ∗ kvOwnAt E (oc.logAfter log) L`; the backend's Put (a dead lease's
   commit refuted by two writer halves), Txn (`txn.Txn.spec`'s `PathsLeaseOk`/rejection), DeleteRange (trivial) prove it;
   quota/capped/corrupt/auth pass it or reject (`kvOwn_rejected`); the class-track consumers (`apply/Results`,
   `uberApplier__dispatch`) forget it (`kvOwn_of_atP`). The latest track: `dispatch.kvSpecL` gains `⌜v3 = true → E.lg =
   true → leaseExactL T rq log o⌝` (from `kvOwnAt_ltHalf` at the caller's `ltHalf E T`), `uberApplier.Apply.kvSpecL`,
   `uberKVC`, `apply.Apply.kvSpecL` gain `⌜∀ o b, out = .dispatched o b → v3 = true → E.lg = true → leaseExactL T rq x.log
   o⌝`; `auth_pass_kvPostFL_nil` takes `dispatchKind rq = .leaseRevoke`. The server (`applyEntryNormal`) drops the new
   conjunct for now (`%HXo, -, #Hdel`): §6 consumes it.
4. **§4 started**: `appliedTableM`, `appliedTableM_false/true`, `appliedTableM_eq_model` in `KVModelM.lean` (checked with
   lean-check, not yet in a full build; it rebuilds ~1270 modules). **Finding:** `srvRest` (`InvRest.lean`) is imported
   by `KVAuthModel`, so it cannot read `kvLeasesOn`. Proposed form (to do): split `srvRest` into a table-generic
   `srvRestT E γr T A` in `InvRest` (`srvRest E γr A := srvRestT E γr (appliedTable γr A) A`, so the off proofs are
   untouched) and `srvRestM on E γr A := if on then srvRestT E γr (appliedTableM true γr A) A else srvRest E γr A` in a
   module after `KVModelM`; `srvRestRp`/`imageLeasesAt` and the auth-on users take `srvRestM E.authOn` (Draft §4's
   "`srvRest` and `srvRestAt`'s callers use `appliedTableM E.authOn`", in a Lean shape that fits the import order).

5. **§4's split done** (approved by etcd-grove-81 as a form, §14 row): `srvRestT`, `srvRest_eq_T` (`rfl`),
   `srvRestT_lg_false` (InvRest); `srvRestM on` (`srvRest` off, `srvRestT … (appliedTableM true γr A)` on),
   `srvRestM_false` (`rfl`), `srvRestM_lg_false`, `srvRestRpM on`, `srvRestRpM_false`, `srvRestRpM_lg_false` (ApplyRDefs);
   `imageLeasesAtT`, `imageLeasesAt_eq_T` (ImageLeases). Full build `build10` at `f0b7821df7`.

**Session 3 (2026-11-15):** the statement switch is DONE (commit after `82b6add2a9`, full build `build12`, `/shared/tmp/auth-lease-s3a/build12.log`):
- Defs: `srvRestM`/`srvRestRpM` moved to `KVModelM` (the snapshot files do not import `ApplyRDefs`); `srvRestRM on`
  (ApplyRDefs); `imageLeasesAtM on` (SnapApplyDefs); M laws in KVModelM (`srvRestT_eq_at`, `srvRestM_eq_at/_open/_close/
  _snoc`, `appliedTableM_cc`, `srvRestM_nil`, `leaseItems_of_noLease`) and ApplyRDefs (`srvRestRM_*`, `srvRestRpM_eq_at/
  _ro/_open/_close/_model`); `srvKVInvsM_rows` (ServerOnDefs).
- Statements at the mode: the five specs (applyEntryNormal, applyEntries, apply, applyAll specBatch/specSnapM,
  applySnapshot specSnapM incl. `hlease : imageLeasesAtM E.authOn` and the frozen rev-5 `hnl`), ModeSpecs.specOn, the
  run/start rows (RunOn, StartOn, AuthCompRows), `srvSnapAppliedG on`, `SnapImageFactsOn.nolease/.hlease` (rev-5 §5).
  The start rows convert at `isServerBuilt_of_gapOn` by `srvRestM_nil` (empty prefix), not transitional.
- `EtcdServer.apply.wp_proofOn` is ported to the M laws for real (no transitional step).
- **§5 started:** `keysLeasesLive_kvRaftOfOn` (KVAuthModel; needs only `LogNoLease log0`: `backendLog` enforces the
  live set, so no admission premise), with `liveSt` and its laws through `applyChange(s)`, `srvOps`, `backendLog`,
  the chain, `dispatchLog`, `kvEntry`, `kvEntryOn`; `kvInvOn_log0`, `kvInvOn_keysLive` (what the callers of
  `specSnapM` need for the new `hnl`). `keysNonEmpty`'s preservation NOT done (needs `kvShapeAll`'s put-key shape).
- TRANSITIONAL sites now (each marked "TRANSITIONAL until the §5 step"): `isServerC_restM` (AuthCompRows) used by
  applyAll's merged send; the `srvRestM_lg_false`/`srvRestRpM_lg_false` conversions in ApplyAllSnap (on branch:
  `snapRecv_imageOnR`, merged send), EtcdServer__applyEntryNormal (both on branches: `irevert HRS HΦ; simp only [hR]`),
  SnapApplyPost (`HrestM`), EtcdServer__run/StopShutdown/NewServerR (the run and stop rows at `srvRestRM K.isOn`, off by `srvRestRM_false`: not transitional), EtcdServer__applySnapshot (lg = false branch: `Hnil` derives `LogNoLease` of the auth-on
  image from `kvInvOn_log0` + `kvRaftOfOn_restorable` at lease mode none; `hleaseI` to the off table), SnapRecvOn and
  ApplyAllSnap (`SnapImageFactsOn` built from the lease-free image); plus the older ones (`grep -rn TRANSITIONAL Proof`).

**Session 4 (2026-11-15):** handoff items (a), (b) and most of (c) DONE (commits `26acfbb48f`, `1239efff42`; full
build `build13` at `1239efff42`, `/shared/tmp/auth-lease-s3a/build13.log`; see the session report):
- (a) `keysNonEmpty` preserved: `neSt`, `opKeysNE`/`opsKeysNE`, `reqKeysNE`, `entryKeysNE` and their laws through
  `applyChange(s)`, `srvOp(s)`, `backendLog`, the chain, `dispatchLog`, `kvEntry`, `kvEntryOn`, `kvRaftOfOn`;
  `reqKeysNE_of_shape` (`kvShapeAll`: a put's key is a point key of the cache's shape), `entryKeysNE_of_plain`,
  `keysNonEmpty_kvRaftOfOn` (KVAuthModel). Not yet used (§6's `kvShapedL` at a leased put takes it).
- (b) the snapshot consumers at the keys-live form: `applySnapshot_walk`'s `hnl` is "every leased key's lease is in
  `Recover`'s `Lr`" (pending items = the image's lease items, each short by `Hkey`), `snapWalkPost`'s `leaseOwn Lr`
  at the image's lease items, `snap_applyKV` at them (`leasesKnown_of_items`, SnapApplyKVLemmas), `snap_srvRest`
  at `srvRestM on` (`srvRestM_close`), `srvSnapApplied_of_walk` at `appliedTableM E.authOn` (its TRANSITIONAL
  `HrestM` gone). `EtcdServer.applySnapshot.wp_proof`'s leased branch (`E.lg = true`) now covers both auth modes:
  the mode's table (`ImageLeasesOn.lean`: `kvEntryOn_table_eq_or`, `kvRaftOfOn_table_{mem,nodup,mono}`,
  `appliedTableM_{nodup,ids_granted,mono_mem,mono_sub,rev_mem,granted_live}`, `kv_grantLog_nodup_on`), the image's
  records by `imageLeasesAtT_recs` (ImageLeases, table-generic), `hnl` from the frozen rev-5 text. The `E.lg = false`
  branch is not transitional (lease mode `none` from `E.lg = false`); its comment relabelled.
- (c) the auth-on image carries the leases (Draft §5's ImageOn/MergedImageOn/SnapSendBranch/snapRecv rows):
  `bkRestAtNAL T` (ImageOn) in `imageRestAtOn` at `kvLeasesOn γk st₀ L`; `mergedImgM`'s table `appliedTableM M.isOn`;
  `bkRestAtM_of_obs`, `mergedCreate_window`, `stop_obs` at `appliedTableM E.authOn`/`srvRestM E.authOn`;
  `merged_imageOn` builds the leased certificate (`kvLeasesOn_none` when `E.lg = false`); `snapRecv_imageOn`,
  `snapRecv_imageOnR` take `srvRestM true`/`srvRestRpM true`, no `hlg`, and give `SnapImageFactsOn` from the image's
  records (`bkRestAtNAL_other`, `restModel_bk_of_NAL`, `image_alarmNAL`, `image_membBucketsNAL`,
  `clusterImageOk_of_NAL`, `imageLeasesAtT_of_NAL`, SnapRecvOn; `nolease` from `keysLeasesLive_kvRaftOfOn`).
  TRANSITIONAL conversions removed: applyAll's merged send (`isServerC_restM` deleted), ApplyAllSnap (on receive and
  on merged send; the lessor-mode block `hEm`/`HElg`/`Hlrev` deleted: unused), SnapRecvOn, MergedImageOn,
  SnapApplyPost (`srvKVInvsM_lg` deleted).
- Left of (c), all bound to §6: the row `γr.kv.lg = false` in `srvKVInvsOn` (KVApplyOn) and its three users,
  `kv_entry_pre_on` (ApplyEntryOn:151, over `plainCover`) and `applyEntryNormal.wp_proofOn`'s two branches
  (v3 = false replay, 1293; v3 = true, 1519). Dropping the row before §6 breaks those proofs: the on branches must
  then cover the revocable mode.

Next (session 5), in order:
1. §6, pure side (KVOutcomeOn/ApplyNormalOn/ApplyEntryOn): `kvShapedL_of_log` at `plainReqL lm` with `keysNonEmpty`
   (a leased put's/txn's lease keys `reqShape k []` from `keysNonEmpty_kvRaftOfOn`); `authOutL_of_kvOutL`/
   `outcomeOn_of_kvOutL` at `plainReqL lm` with the lease verdict (`KVAuthBridge.leaseOk_iff`) and `leaseExactL T`
   at `T = (appliedTableM true γr A).ids` (`appliedTableM_eq_model`, `pre = []`); `kv_entry_pre_on` at the mode
   (`plainEntryOn γk.lm`, no `plainCover`); `kvOn_after_kv`, `authTie_of_kvOutL` likewise.
2. §6, `applyEntryNormal.wp_proofOn` v3 = true: the KV arm consumes the dropped `leaseExactL` conjunct (`%HXo, -,
   #Hdel` → keep it); new grant arm (the off arm's `srvEver_applyPre`, `kv_entry_grantFresh`, `grantReqA_of_res`,
   at the mode's table) and revocation arm (S2's `LeaseRevoke.specL`, `revokeOwn`, `ltHalf`, `revokeRestA`; the
   KV side new: the lease's keys' deletions committed, Draft §6 r2 N4); the rest at `srvRestM true` (no
   `srvRestM_lg_false`).
3. The replay branch (v3 = false): `srvRestRpM true` at the mode's table; at `v3 = false` `kvEntryOn` keeps the
   table (`dispatchTable` with `v3 = false`).
4. Drop `γr.kv.lg = false` from `srvKVInvsOn` (KVApplyOn:401) and from its provers (`NewServerAllocOn`,
   `srvClusterBootOn_alloc`); fix the destructurings of its pure row (`Hrows.2.2.1` etc. shift: grep `srvKVInvsOn` in
   ReadOn, ApplyNormalOn, KVApplyOn, ServerOnDefs (`srvKVInvsM_rows`), AuthCompRows (`isServerC_lm`), ModeSpecs,
   ApplyAllSnap (`Hcmlg`), EtcdServer__run/apply, WatchSrv, MainServe).
5. The land-stop checks (below, "Build").


**Session 5 (2026-11-15): STOPPED at a finding (ledger 2026-11-15, "the latest track's certificate premise for a
leased put or transaction").** The KV branch of Draft §6 cannot be proved for an admitted leased put or leased
transaction: the latest triples' premise `certPreVW … (kvOutL …)` becomes, through `certPreW_inner`, the class track's
`certPre` over every `backendStep` outcome, and `backendStep` admits an applied put of a lease not live (and an applied
transaction without `PathsLeaseOk`), whose log `kvNxOn` cannot certify. Options in the ledger entry ((1) the certificate
at the live set `T`, recommended as its own reviewed change; (3) narrow S3a to no leased put/transaction). Waiting for
etcd-grove-81. Done this session (pure, option-independent, checked with `etc/lean-check.py -a`, not yet in a full
build): `leaseOk_of_leasePassedL`, `not_leaseOk_of_leaseRefusedL` (the bridge; no shape needed), `kvGrantedL_of_kvOutL`
(every authKV kind), `backendTable_kv`, `chainTable_kv`, `backendLog_of_step` (a KV request's backend outcome is
`backendLog` given `plainCover ∨ leaseExactL lt.ids`), `outcomeOn_of_kvOutLL` (at `plainReqL lm`), `revokeLog_eq_backendLog`
(`liveSt` + `0 ∉ ids`), `outcomeOn_of_kvOutL_revoke` (KVOutcomeOn); `leaseShapedL_of_keysNE`, `kvShapedL_of_logL` (no
`plainCover`; ApplyNormalOn). Not blocked by the finding, next whatever the decision: the grant arm and the revocation
arm of `applyEntryNormal.wp_proofOn` (a revocation's certificate is the model's: `outcomeOn_of_kvOutL_revoke`; it needs
`liveSt` of the model's state, `liveSt_kvRaftOfOn`, and `0 ∉` the table's ids, from `appliedTableM_ids_granted`-style
facts), then the replay branch. The row `γr.kv.lg = false` stays until the KV arm covers the revocable mode.

**Session 5, continued (2026-11-15): decided by etcd-grove-81, (3) now, then (1) as stage S3a2.** Done:
- Rev 7 (Draft §15, ledger decision): `plainReqL lm := plainReq` (`plainReqL_iff`); destructurings of the old
  disjunction fixed (KVAuthModel, KVOutcomeOn, SnapRecvOn, ImageLeasesOn, SnapAuthRecover). Commit `…rev 7`.
- `kv_entry_pre_on` at the mode (no transitional step; grants/revocations are no KV kind).
- `applyEntryNormal.wp_proofOn` at `srvRestM true` throughout (no `srvRestM_lg_false`): new `RestOn.lean`
  (`appliedTableM_true_snoc/_eq/_nonLease/_nodata`, `srvRestM_keep`, `srvRestM_nodata/_admin/_applyP/_applyP0`).
  The replay branch (v3 = false) is DONE at the lease mode: plain, grant and revocation entries all by
  `Apply.spec` (`plainOrCmpG_of_entryOn`, `revokeOwn_take`), at `srvRestRpM true`. Commit `fdd1d88b44`; checked
  with `etc/lean-check.py -a` (0 errors).
- What is LEFT of the transitional row: the two `exfalso` bullets in the v3 = true data branch of `wp_proofOn`
  (marked "TRANSITIONAL until the grant arm" / "… revocation arm"), and the row itself in `srvKVInvsOn`
  (KVApplyOn) with its docstring. `grep -rn TRANSITIONAL Proof` lists exactly these.

Full build GREEN at `fdd1d88b44` (`/shared/tmp/auth-lease-s3a/build14.log`, flock + 64G).

**Next (session 6), in order:**
1. The grant arm (v3 = true), modelled on the cluster-request branch (`hA`, `Apply.spec`, auth passes a grant
   through: not `authChecks`): `applyStep_grant`, `kvEntry_grant`; the table after is `kvTable` (the model's write
   branch: a grant is no `authKVKind`, no admin), so generalize the `tail_on` macro to take the table `lt'` (it
   hardcodes `kvLeasesOn γr.kv srvAuthSt0 A`; `kvApplied_nextOn` already takes any `lt'`); certificate: the log
   kept (a `kv_certPre_keep` for a grant: `apply.chainStep_grant_logAfter`); `srvEver_applyPre` with a new
   `kv_entry_grantFresh_on` (port of `kv_entry_grantFresh` over `kvInvOn`'s `kvGrantIds`); `srvGrantIf_permPG`;
   `grantReqA_of_res`; `srvRestM_applyG` (port of `srvRest_applyG`'s `lg = true` branch at the auth-on table,
   `appliedTableM_true_snoc` + the write branch giving `dispatchTable`); the result's not-NOSPACE at the auth chain
   (`applyResultIs_notNoSpace_grant` is at `alarmChain false …`: port); `authTie_nonKV`; `grantArM_of_resW`.
2. The revocation arm (v3 = true), modelled on the KV branch (`hK`, `kvSpecL`: `authKVKind .leaseRevoke`):
   certificate from `outcomeOn_of_kvOutL_revoke` (needs `liveSt` of the model state: with rev 7 the model's log has
   no leased key, `LogNoLease`, so `liveSt` is immediate; and `0 ∉` the table's ids: a `kvRaftOfOn` port of
   `kvTableOf_ne0`); `kvShapedL_of_logL` + `keysNonEmpty_kvRaftOfOn`; `revokeOwn_take`; the post's
   `revokeIdsA`/`revokeRestA` at the model's table after (refused at the latest state: kept; applied:
   `backendTable`'s filter; port `revokeA_table`/`srvRest_applyR` to the auth-on table); `revokeArM` from
   `revokeAnsRA` (`InvRequest.lean:2031`); not-NOSPACE (`applyResultIs_notNoSpace_revoke` at the auth chain);
   `authTie` of a revocation (check `authTie`'s kind guard).
3. Drop `γr.kv.lg = false` from `srvKVInvsOn` (KVApplyOn) and its provers (`NewServerAllocOn`,
   `srvClusterBootOn_alloc`); shift the destructurings (`Hrows.2.2.1` → `Hrows.2.1` etc.: grep `srvKVInvsOn` in
   ReadOn, ApplyNormalOn, KVApplyOn, ServerOnDefs `srvKVInvsM_rows`, AuthCompRows `isServerC_lm`, ModeSpecs,
   ApplyAllSnap `Hcmlg`, EtcdServer__run/apply/applyEntryNormal (`obtain ⟨-, -, hlmE, -⟩ := Hrows`, `Hrows'.2.2.1`),
   WatchSrv, MainServe).
4. The land-stop checks (merge lean, full build under flock + 64G, tcb 870/4, gen-interface with only Alloc3On.txt,
   bounds/mode, no closed statement changed, `grep -rn TRANSITIONAL` empty, STATUS/handoff/status-history). STOP
   before `etc/land.sh`.

**Session 6 (2026-11-15): S3a's proof DONE, at the land stop.** Commits `9c2f582bd1` (the grant and revocation
arms), `b2550e6a1d` (the transitional row dropped):
1. The grant arm (v3 = true): `apply.Apply.spec` (the auth layer passes a grant through), the log kept, the table
   the model's step (`kvEntryOn_grant`: the third branch of `kvEntryOn`, `dispatchTable` at the auth-on chain);
   `srvRestT_applyG` (`srvRest_applyG` at any table), `kv_entry_grantFresh_on`, `kv_certPre_grantOn`,
   `applyResultIs_notNoSpace_grantOn` (`dispatchStep_start_grantB`). All in `RestOn.lean`.
2. The revocation arm (v3 = true): the latest-state triple `kvSpecL` (the auth layer checks a revocation);
   `revokeOn_after` (refused: the model's table kept; applied: `backendTable`); the certificate
   `kv_certPreVW_revoke_on` over `outcomeOn_of_kvOutL_revoke` (`liveSt` from `kvInvOn_log0`, `0 ∉` the table by
   `kvRaftOfOn_ne0`); `kvShapedL_revoke` from `keysNonEmpty_kvRaftOfOn`; `srvRestT_applyR` with the refusal;
   `applyResultIs_notNoSpace_revokeOn` (the auth error told apart). The table after needs the empty raft prefix
   (`srvKVInvsOn`'s `pre = []`) to be the model's state the outcome met.
3. `γr.kv.lg = false` dropped from `srvKVInvsOn`; `acModesOk` on: `cmp = false` only (`srvKVInvsC`); NewServer no
   longer proves it. `grep -rn TRANSITIONAL` is empty. The local macro `tail_on` takes the table after the entry.
4. Land-stop checks (2026-11-15): lean not moved (`c3da59fa29` merged); full build GREEN under flock + 64G
   (`/shared/tmp/auth-lease-s3a/build15.log`, 17537 jobs); `tcb-report --check` 870 axioms, 4 sorries; every
   `etc/api` list's `gen-interface --check` passes, no interface differs from lean (the Alloc3On change is a
   proof body only); bounds ok (351); mode gate: S3a's findings classified (`model`: the auth-on table's rows;
   `unmoved`: `specSnapM`'s frozen `hnl`), baselines raised (etcdserver lit-mode 156→252, match-mode 76→78,
   client/v3 lit-mode 18→22; commit `4f34346b9e`); no closed theorem statement changed (the diff in
   `Proof/github_com` is proof bodies). STOPPED before `etc/land.sh`.

**Stage S3a2 (after S3a lands; its own Scope and Freeze; 3–6 agent-days; S3b's leased put waits on it).** Leased
puts and leased transactions in the auth-on apply thread (ledger 2026-11-15, option (1)). Freeze items:
- `certPreT E c rq log T` in place of the class track's `certPre` for KV requests: the certificate of the outcomes
  that are lease-exact at the live set `T` (`apply.leaseExactL T`), with the class track's `leasesLive` at `T`
  (`kvOwnAt E log T`, split at the top layer from the two `ltHalf`s);
- the backend's `Put`/`Txn` take the certificate only when the lease is live (today `applierV3backend__Put.lean:88-95`
  takes it before the lease check);
- the latest track's `X` gains `leaseExactL T` (`certPreW_inner`, `Apply.kvSpecL`, `uberKVC`,
  `uberApplier.Apply.kvSpecL`, `dispatch.kvSpecL`: the exported `apply_*_kv_latest` change);
- `plainReqL` widened back to Draft §1's text; §6's KV arm over `outcomeOn_of_kvOutLL` (session 5's lemmas:
  `backendLog_of_step`, `kvGrantedL_of_kvOutL`, `kvShapedL_of_logL`).

## Pitfalls

- `kvStOn` is `@[reducible]` but `rw` does not see through it: write `kvStateOf (kvModelOn …) (kvLeasesOn …)`
  in goals that are rewritten.
- In an Iris proof, `cases hon : E.authOn` rewrites the goal but not the Iris context (an `iexact` of a hypothesis at
  `E.authOn` then fails at `false`): split with `by_cases hon : E.authOn = true` and rewrite where needed.
- `srvRestM false E γr A` is `srvRest E γr A` by `rfl` but `iexact` does not unify them (a `match` on the mode):
  `rw [srvRestM_false]` first.
- With `apply.DispatchKVL` imported, `and_false` can be ambiguous in `simp only` (`BI.and_false`): use
  `_root_.and_false`.

- The latest-state refusal must be stated in `refusedL`'s form (`leaseRefusedL`), not `¬ leasePassedL`:
  `latestOk` is vacuous at `hs = []` and in mode `any`.
- `isAuthStoreL`'s admin clause gives only the latest verdict; the lease class (`leaseKeysClass`'s
  admin disjunct) needs a recorded state: the probe adds `□ ∀ hs, L hs -∗ L hs ∗ auth.latestSnap M hs`
  (real store: `latestResC_snap`).
- The model's refusal guard `isKVKind` excludes `.leaseRevoke`: the triple-state model's guard must
  add it (`authKVKind`), or a refused revocation is applied.
- `txn.putsW`, `lease.keysOf`, `kvGrantedPerm` (Scope Draft names) do not exist; the probe defines
  `putsW` (mutual `opPuts`/`opsPuts`) and states key sets over `I.lookup ⟨k⟩ = some id`.

## Build

Targeted: `systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
<modules>`; check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`. Full builds
under `flock /shared/tmp/etcd-grove-build.lock`. `TMPDIR=/shared/tmp`.

## Left (follow-ups)

- **The auth-on lease table's literal modes** (mode-gate raise accepted by etcd-grove-81, 2026-11-15): S3a raised the
  mode baselines (etcdserver lit-mode 156→252, match-mode 76→78, client/v3 lit-mode 18→22) with `appliedTableM true`,
  `srvRestM true`, `srvRestRM true`, `srvRestRpM true`, `kvModelM`/`kvStM` at literals; S3a2 should try to reduce the
  literal-`true` uses (state the auth-on arms' lemmas at `srvRestT` and the slot's `C.isOn`).

- **The empty-prefix fact ties the auth-on server to fresh starts** (S3a rev 5, `srvKVInvsOn`'s `γr.raft.pre = []`):
  an auth-on restart (future work) has to revisit it (the model's table folds over the applied entries, `srvRest`'s
  over the raft prefix and them).
- A revocable auth-on cluster's snapshots: carried by S3a §5 (the image's table, `keysLeasesLive`).
