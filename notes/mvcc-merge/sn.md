# Track SN: the snapshot send/receive/apply (`origin/lean` → `mvcc-api` merge, 2026-11-06)

Resolved and staged (`git add`) 19 files; 7 deleted (`git rm`). No commit and no build were run.
Rule applied everywhere: the store's part is ours (the API), the rest is `lean`'s (auth-on pair
P5/P6.2/F9, lease-expiry S2–S4 with `Recover` of the image's records, R2b-3c/3d stop channels,
R2d `bFile`, `WTNames`, WAL `rnWalTokA`/`rnWalHanded`). F2 is dropped.

## Per file

**Deleted (ours' deletion kept; `lean`'s edits there were F2 or R-D1 over mvcc's internals):**
`M2ApplyDraft`, `M2StorageDraft`, `M2StorageDraftRestore`, `RestorePre`, `RestorePreM`,
`SnapApplyCloser`, `SnapRestoreM`. `SnapApplyPost.lean` (not mine) still imports `SnapApplyCloser`.

**Specs**
- `Spec/.../EtcdServer__snapshot.lean`: `lean`'s `rnWalTokA γn … ∗ rnWalHanded γn ai` plus ours'
  `threadTok` (pre and post); ours' KV `□ isMvcc kv E.γ ∗ ⌜kv = E.kv⌝`.
- `Spec/.../EtcdServer__snapshotIfNeededAndCompactRaftLog.lean`: the same; `srvWTTaken γp.cnt`
  (`lean`'s `WTNames`), ours' KV.
- `Spec/.../EtcdServer__applySnapshot.lean`: `lean`'s `specSnapM` (one spec over `E.authMode`,
  lease-expiry's `hlease : imageLeasesAt`, `hAA'`, `hpre0`, `hlmk`, `hany`, `hauthI`,
  `lessorModeIs`, `srvStopChans γ d`, `bOpen … (srvOpenQ …)`, `snapAuthResM`). Mvcc-facing part ours:
  `hkb : E.BkTie = srvBkTie d`; `A' u`, `hxA`, `hst` at **`kvModelM E.authOn`** (ours had
  `kvModel`, mode off only); `srvKVAddr s ↦□ E.kv ∗ mvccImage D … u ∗ E.Cp …`; `lessorInv`/
  `lessorModeIs` at `mvccLeases E.γ`; post `srvSnapAppliedM E.authOn … d A' …` (no `R r`). Dropped:
  `hwq`, `R`, `hpre`, `hRok`, `r`, `hcc`, `hkI`, `srvKVCloserW`, the watchable store, `certOk`,
  `restoreRcptM`, `crevPermAt`, the import of mvcc's `RestoreImageOpen`.

**Proof modules**
- `SnapRO`: `lessorApplyOk` at `lean`'s `lessorBackend … T Ln R` with `Ln := RW`, `R := apply.bkRT d`
  (plan risk 4); `srvRestOwnH_lens_revoke` ours (`rbPart`, no store names) + `lean`'s `M`;
  `clusterApplyOk` ours (tie) + `lean`'s `M`; `srvSnapRO` ours (tie, `isMvcc`, no `cm`/`watchQ`)
  + `lean`'s auth buckets, `E.authMode` in `E.RO`, lessor mode (at `mvccLeases E.γ`);
  `srvSnapRO_succ` ours + `E'.authMode`, no `hcm'`. **`srvStopChans γA d` restated at
  `mvcc.api.mvccW d.gx`** (was `mvcc.lateWD d`). `srvSnapRes s E γA`: `lean`'s (stop channels,
  `srvOpenQ`, `bFile`) at the tie, no closer. `srvSnapApplied` (ours, moved here) + `lean`'s
  `srvStopChans γ' d'`, `bFile d'.γB bp`, `E'.authMode`. `srvKVCloser`/`srvKVCloserW` deleted.
- `SnapApplyDefs`: ours' header/imports + `SnapApplyAuthM`; lemmas both sides (`kbP_mk`,
  `kbgx_mk`, `rep_two`, `rdStock_split2`, `ltHalf_agree_upd`, `ever_live_modeM` at `mvccLeases`);
  `kbRT_some` dropped. `snapWalkPost`: `lean`'s (params `Lr recs U reqOf`, live/ever sets,
  `hooksOk`, `isStopChans` 5-arg, `plHookRO`, `restSet E.authMode`, `srvOpenQ`, `bFile`,
  `snapAuthRowM`) with ours' store (`mvccOpen`, `mvccBackend`, `wSt`/`crOwn` at `kvModelM E.authOn`),
  W = `mvccW d'.gx`, no `R r`. `srvSnapAppliedG/On/M`, `_G_off`, `_M_of_G` kept here (they need
  `AppliedOn`, which imports `SnapRO`), restated as `srvSnapApplied` (tie, `kvModelM on`, `isMvcc`).
- `SnapRecvFacts`: `SnapImageFacts` ours (`hst`) + `lean`'s `hlease : imageLeasesAt`; `nolease`
  dropped. `snapRecv_image` body: ours + `lean`'s `plainLogM` and `srvRest_open`/`restLeasesWith`.
- `SnapApplyWalk`: statement `lean`'s (mode, `hRecOn`, lease records, `r0`, `hTODO`) + ours'
  laws/`u`/`hxA`/`hst` (by mode); dropped `hwq`, `hRst`, the backend's internal specs, `hLSR`,
  `hUSR`, `hWrite`, `R r hkI …`. Body: `lean`'s steps with W/`γB` substituted, ours' restore
  (hunks 6–12, 14–17, 23).
- `SnapApplyIsServer`: ours + `on` (`isServerM`), `srvAtomicsM_snapE`.
- `SnapApplyNames`: `snapE` ours (tie) + `E.authMode` in RO; `snapE_lg/lm` added; `snapE_kb`
  dropped; **`srvAtomicsM_snapE` restated as an equality by `rfl`** (was an entailment over `p'`).
- `SnapApplyKV`: `snap_applyKV` ours + `lean`'s `on`/`st`/`L`/`ltHalf`/`uberIs`/`kvAuthM`, deleter
  as `∃ rd, rdOwn ∗ mvccDeleter rd E.γ`; `kvAuthM_snap` at `d'` (no `p'`, `γB`).
- `SnapApplyKVLemmas`: ours (`lean`'s `leasesKnown_restore`, `kvOwn_snap` dropped).
- `SnapApplyOpen`: ours wholesale (`lean`'s edits all F2 / `rdAt` step 2).
- `SnapApplyOptsLemmas`: ours' three store lemmas + `lean`'s `M`. The rest of the file (from
  `snap_isApplyLessor`) was red on ours and untouched.
- `SnapApplyRest`: `lean`'s (`restSet`, live set, grants, requests, ever) at `snapE … d' …`.
- `SnapApply`: `srv_be_swap` ours + `γp : WTNames`, `srvWTStockInv γp.cnt`.
- `SnapSendBranch`: F2 dropped (`spec_of_specF2`, `srvBeSnapOk_of_backend`, `srvBeSnapOk_window`,
  `soleWriter_idxWf`, `apply.cmpObs`, `windowObs*`, `mergedObs`, `mergedObs_of_M`,
  `mergedObsM_of_obs`); kept `lean`'s `bkRestIf_of_rb`, `bkRestAtM`, `bkLendW_none`; new
  `mergedImgM M lg` (`lean`'s `mergedObsM` with ours' store part: `imageStOk` + `mvccImage`).
  `mergedCreate_window`: ours + `γp : WTNames`, `lean`'s lent buckets `SA QA RA hSA` and
  `bkLendW E SA QA RA` (post gives `RA` and the lent buckets' fact); `hpos`/`hlen` not taken.
  `merged_image`: ours.
- `ApplyAllSnap`: per hunk, `lean`'s structure (`kvInv_authOn`, `HauSK`, `HlpM`, `specSnapM` call,
  `hoff'`, `srvOpenQ_off`, `bkLendW_none`) with ours' store args.
- `EtcdServer__snapshot` / `…IfNeededAndCompactRaftLog` (proofs): `#Hwh` and `Htt` both, `lean`'s
  `γn hγn hpre` args, `lean`'s `srvSnapStor` unpacking.

## MERGE-TODOs

- `close` (pending the user's decision, plan risk 1): `SnapRO` (closer deleted, `srvSnapRes`,
  `srvSnapApplied`), `SnapApplyDefs` (`srvSnapAppliedG`, `snapWalkPost`'s closer parts),
  `Spec/…applySnapshot` (closer), `ApplyAllSnap` (`HKC`), `SnapSendBranch`
  (`mergedObsM_of_obs` was shared with `StopImage`).
- `deleter-after-recover`: `SnapApplyDefs.snapWalkPost` and `SnapApplyWalk` (rebuild
  `mvccDeleter rd E.γ` after `lessor.Recover`, from `KV.Write.contract`; `lean`'s `rdAt` rebuild
  text left below the marker).
- `snap-leases`: ours' `hnl : LogNoLease` (spec, walk, `SnapImageFacts.nolease`, `snap_applyKV`)
  dropped, because `lean`'s lease-expiry restores the image's leases. `KV.Restore`'s
  `leaseOwn (mvccLeases E.γ) L ∅` has to be met at `L := Lr` (`Recover`'s live set), and
  `leasesKnown Lr` replaces `leasesKnown []`. `SnapRecvFacts.hlease` needs `lean`'s `bkRestAtL`
  image, but the merged `InvImage.imageRestAt` is ours' `bkRestAt` (see below).
- `send` / `send-leases`: `mergedCreate_window`'s body is ours. It needs `lean`'s lending and the
  lease records (`srvRest_open`'s `f`). Its post should become `mergedImgM E.authMode E.lg`, and
  `merged_image`/`merged_imageOn` should consume that.
- `walk`: `SnapApplyWalk` body (a textual merge), `SnapApplyKV` body (ours, mode off),
  `ApplyAllSnap` (`HxA`/`hst` at `kvModelM`), `srvAtomicsM_snapE` (`rfl` not checked).

## Spec changes (the server's own)

- `applySnapshot.specSnapM` (vs `lean`): premises `hkb : E.γ.kb = some d` → `E.BkTie = srvBkTie d`.
  `hwq R hpre hRok r hcc hkI` → `A' u hxA hst` at `kvModelM E.authOn`.
  Resources: closer, watchable store, `certOk`, `restoreRcptM`, `crevPermAt ×2` →
  `srvKVAddr s ↦□ E.kv ∗ mvccImage D … u ∗ E.Cp (crevOf …)`. `E.γ.leases` → `mvccLeases E.γ`.
  Post: `srvSnapAppliedM … d R r A' …` → `… d A' …`.
  (vs ours') `hnl` dropped; `kvModel` → `kvModelM E.authOn`.
- `srvSnapApplied*` post: `x'.log = [[],[]] ++ R ∧ x'.crev = r.crev` → `x'.log = kvModelM on γr.kv A'`
  and `x'.crev = crevOf γr.kv A'`, without the closer, with the KV `□ isMvcc`.
- `snapshot.spec`, `snapshotIfNeededAndCompactRaftLog.specBatch`: ours' `threadTok` added to
  `lean`'s (the same change ours made).

## Non-conflicted files that will break

F2 names (`git grep -l -E 'kbTieInit|kbCrev|restoreTie|kbBoot|CmpTies|spec_of_specF2|pvckInit|lateWB|kbTrack'`):
- `BuildLemmas.lean` (UU, another track): comment only. `srvStopChans_boot` should target
  `srvStopChans` at `mvcc.api.mvccW d.gx`.
- `InvBoot.lean:417`: `newPostK … (fun γB => mvcc.lateWB d.gx γB)` → `(fun _ => mvcc.api.mvccW d.gx)`
  (`bootBackend.law`'s `newPostKP`).
- `InvRestart.lean:339–523`: `lateWBR` (over `lateWB`'s `pvckOwn` arm) → define it as
  `mvcc.api.mvccW gx`, or drop it, and use that at `:523`.
- `NewServer.lean` (630, 642, 706, 841, 943, 1009, 1186, 1525, 1796): `mvcc.lateWB d.gx d.γB` →
  `mvcc.api.mvccW d.gx`. The `pvckInit`-based `newPostK` at 630 → `bootBackend.law`.
- `Results.lean` (880–1155): drop `mvcc.kbTieInit_off` (922). `mvcc.lateWB d.gx d.γB` →
  `mvcc.api.mvccW d.gx` at 890, 973, 1124, 1155. This changes a top-level result's text, so it needs
  the plan's approval.
- `SnapRO.lean`, `SnapSendBranch.lean`: comments only.

Snapshot-path files (not mine) over my restated names or mvcc internals:
- `SnapApplyPost`: `snapWalkPost … R r` → no `R r` plus `Lr recs U reqOf`; imports the deleted
  `SnapApplyCloser`; `isWatchableStore`, `keyImageM`, `certOk`, `txn.isKV`.
- `SnapApplyOpts`: `mvcc.lateWD` → `mvccW d'.gx`; the watchable store → `isMvcc`.
- `EtcdServer__applySnapshot` (proof): `srvSnapAppliedM_of_G … d R r A'` → `… d A'`;
  `E.γ.leases` → `mvccLeases E.γ`.
- `ApplyAllSnapOn` (#7-on), `SnapRecvOn`, `MergedImageOn`: over `keyImageM`, `restoreRcptM`,
  `crevPermAt`, `certOk`, `mergedObs`(M). Restate them as `ApplyAllSnap` / `SnapRecvFacts` /
  `mergedImgM`.
- `SnapApplyAuthM.snapAuthRowM`: no mvcc names in its body, but the file uses `E.γ.kb`,
  `E.γ.leases`, `E.s`, `lease.rdAt`.
- `StopImage`, `StopShutdown`: use `mergedObsM_of_obs`, `apply.windowObs`, `srvKVCloser`,
  `soleWriter_idxWf`, all dropped (`close`).
- `CmpSupply`: `srvKVCloser` → `srvKVCloserW` (deleted; obsolete under the API's `cmpOwn`).
- `NewServer:1654–1656`: builds `srvKVCloser`/`srvKVCloserW` for `srvSnapBoot` (now without the
  closer). `AuthCompRows:782`: `mergedObsM`.
- `InvImage` (resolved by another track): `imageRestAt` is ours' `bkRestAt`. `lean`'s lease-expiry
  used `bkRestAtL` (the image's lease bucket holds the live leases' records) on both the sender
  (`merged_image`) and the receiver (`SnapRecvFacts.hlease`). Restate `imageRestAt` with
  `bkRestAtL` gated by `lg`.

## API weakness noticed

- None in the API itself. The one gap is the restore's leases: `KV.Restore.contract` takes
  `leaseOwn (mvccLeases γ) L ∅` with every pending item's lease in `L`. That is satisfiable after
  `lessor.Recover` (live set `Lr`) once the image certificate says the image's leases are `Lr`
  (`imageLeasesAt`). Ours' proof avoided this with `hnl`, which is false in a cluster that grants
  leases.
- Shutdown (`close`) is the known risk 1.
