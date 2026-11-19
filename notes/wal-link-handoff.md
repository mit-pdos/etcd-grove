# WAL link: handoff

## START HERE (2026-11-19 q, lean merged (pin f551); clients edited, NOT yet checked; first full build queued)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean df37bd5157 merged (9bdb9cc03f): pin f551a1b46,
  `--packages=/shared/tmp/manifest-f55.json` everywhere, `.lake/package-overrides.json` = its copy; gen-init
  with `PERENNIAL_DIR=/shared/perennial-f551a1b46`. Full build: `/shared/tmp/build-slot.sh etc/timed-build.py
  --packages=/shared/tmp/manifest-f55.json` (log `/shared/tmp/wallink/b-merge1.log`).
- **Merge notes:** lean moved `isRNMemStor_of_memstorage`/`raftNode_of_{Start,Restart}Node` to
  `NodeBridgeLinked`/`NodeStartLinked` (our edits applied there); tier-baseline gained `RaftModel.Laws ->
  proto.SizePb` (defs->proof, as MarshalPb/UnmarshalPb).
- **Edited in ef3559e6a8 (unchecked):** applySnapshot spec/walk/proof (`(γw : RNNames GF) (q : Qp)` last,
  `rnWalTokA` in and out, payload `walSnapRec`, `∃ h, isWalStorage (mkOk stp) h ss` premise, Release via
  `walRelease_spec`+`rnDur_read_au`, `hRel`/`hstp` gone), ApplyAllSnap (srvSnapRO's last conjunct `#Hsws`),
  StopApi (`γrn.wal.h.dir = …`), StopShutdown (srvFiles' `∃ a`), NewServer/NewServerR (bootOk/restartOk_start's
  `h`, `Hνh` from rnDurInv, NodeStart's `#Hsws Hrd1 Hrd2`, `Hrnss`, `isWalStorage_ptr`).
- **F2:** membership bound needs NO new premise: `srvRaftLogInv` now carries `γ.raft.vs.length < 2^16` (from
  `BootCore`'s `idPfxsOf_ok`, at both allocs); `srvRaftLogInv_cfg`, `srv_csF2`, `srv_snapshotValid_F2`
  (RaftLoopFreeze), `walSnapCanon_enc_len` (Codec). raftNode__start's two sorries and snapshot's HF2z/e/i gone.
  **Left: one sorry `Hm1` in EtcdServer__snapshot** (metaRoC canonical: `ep.confState`'s AutoLeave pointer set;
  needs `epCsVoters` at `csPts … true` from applyConfChange (node.ApplyConfChange gives true), received snapshots
  (rnApSnap: ownSnapS), restart (raft's Snapshot spec after InitialState), and raft's CreateSnapshot spec to keep
  it through `proto.Clone`).
- **Next:** build errors in order; examples (drop `rnNewStorageOk` from etcdstart.premises via
  `rnNewStorageOk_holds`, linked by hand), P2, tcb/collections/interfaces/Links, examples' Go, closed-statement STOP.
- **Pitfalls:** never two lean-check files needing rebuilds at once; `--split` spurious kernel error on raftNode__start.

## History

### START HERE (2026-11-19 p, clients in progress: raft-loop side done, snapshot/apply/boot side next)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; pin 6d365ee1a, `/shared/tmp/manifest-6d3.json` everywhere
  (lean now HAS the f551 merge, df37bd5157: merge it next, then manifest-f55 + package-overrides, full timed rebuild). Full builds: `/shared/tmp/build-slot.sh etc/timed-build.py --packages=<manifest>`.
- **Done this session (lean-check 0 errors each unless noted):** specs+proofs `newRaftNode` (`ss` param, `γ.ss = ss`),
  `bootstrappedRaft.newRaftNode` (`wal = ν.h.w`, `isSnapshotter ss`, post `isWalStorage st γw.wal.h γw.ss ∗ walStorRd ∗
  walStorRd`), `raftNode.onStop` (premise `walCloseOk` gone), `raftNode.stop`, `raftNode.start` (premises gone; both
  `Save` sites: entries via `rnDur_viewOk` + `rnEntsSized_walSave`, `hsOptC` from `rnReadyData`/`rnReadySnap`, refused
  batch → `lg.Fatal`; `SaveSnap` via `walSaveSnapC_spec`); `InvWal` (`rnDur_viewOk`, `rnDur_read_au`); `WalApi`
  (`isWalStorage` carries the storage's `s ↦□ ss`, `isWalStorage_ss_agree`; `walSaveEntOk_of`, `rnEntsSized_walSave`);
  `InvRaftNode` (`rnWalTokA` carries `isWalStorage`; `rnReadyData`/`rnReadySnap` carry `hsOptC`); `RaftLoopFreeze`
  (`srvSnapMetaC`, `srv_ownSnapS_metaC`, `walSaveSnapC_spec`); `SnapTake` (`srvSnapDisk` without the contract,
  `srvSnapDir` with `∃ h, isWalStorage st h ss`), `SnapRO` (same, last conjunct). `NodeStart` (both specs),
  `EtcdServer__snapshot` spec+proof (Release via `walRelease_spec`+`rnDur_read_au`; `storage.releaseOk` →
  `storage.snapOpensOk`; imports RaftLoopFreeze), `InvRun` (`srvSnapDisk_of_RO` simplified). Edited, NOT yet
  checked: `snapshotIfNeeded` spec, `InvBoot` (`walCreateOk` dropped from
  `bootstrapContract`, approved §5), `InvRestart` (`srvFiles` over `∃ a : WalA`, `walSaveOk` dropped), `applyAll` spec
  and `InvRaftLoop` payloads (`walSnapRec`).
- **F2 sorries (OPEN, temporary, marked `F2`):** `raftNode__start` SaveSnap: `ConfState ≠ walCsZero`, `encSnap < 2^40`;
  `EtcdServer__snapshot`: the metadata's `metaRoC (srvSnapMetaC …)` (raft's `ConfState()` content for `ep.confState`),
  `ConfState ≠ walCsZero`, `encSnap < 2^40`, `ai < 2^64-1`. The received snapshot's content is already canonical
  (`ownSnapS`'s `csSet … true`, `pbMsg ConfState []`); what is left is a non-zero conf state and a size bound.
- **Next, in order:** applySnapshot spec ( add `rnWalTokA γw (srvRAddr s) q` in and out,
  payload `walSnapRec γw.wal.h`, `hstp` → the premise `∃ h, isWalStorage (mkOk stp) h ss`, its proof in SnapApplyWalk), then the rest of
  `grep -rlE "rnWalTok|walOf|walBaseLb|isWalStorage|storageSnap|rnStorageOf|walReady|walSaveOk|walCloseOk|walCreateOk|releaseOk|WalNames\b|walFiles|srvFiles" Proof Spec`
  in import order (ApplyAllSnap, SnapApplyWalk, InvRun, InvRestart users, NewServer(R), StopShutdown, EtcdServer__run,
  AuthCompRows, examples' Defs/StartRes/OneMember); then F2, P2, merge, build, tcb, collections, interfaces, Links.
- **Pitfalls:** never two lean-check files needing rebuilds at once (the two `lake setup-file`s race: "no such file");
  `--split` gave a spurious kernel error (`_proof_1_34`) on raftNode__start: check it without `--split` (0 errors, 142 s); `rnWalTok_open γ r q $$ Hwt`
  (no storage argument now).


### START HERE (2026-11-19 o, 0009 proved through the server's Save law; InvRaftNode done; clients next)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; pin 6d365ee1a, `/shared/tmp/manifest-6d3.json` everywhere.
  Merge the origin merge (pin f551a1b46, manifest-f55) when it lands on lean. Full builds:
  `/shared/tmp/build-slot.sh etc/timed-build.py --packages=<manifest>` (report the build id).
- **Fork fix 0009** (user-approved, pushed `goose-lean-walfs3-fp9` d3feef9bc): pinned, examples' go.mod bumped,
  `etc/goose.py --check` (etcd, etcd-wal) passes; WAL Go suite passes but TestWALByteMix (by design).
- **Done, lean-check 0 errors each** (forms ACCEPTED by etcd-grove-03, questions.md 2026-11-19): `WAL__Save` (pre-lock
  loop, refused arm, `hfit` → room), `RaftModel/LawsEnt`/`Srv`/`Laws` (SizeLaw), storage `Save`, `WalApi` (Save law
  error arm, `isWalStorage_intro`), `RnNewStorage` (`walSave_law` split on size, `rnNewStorageOk_holds`), WalTester
  `member__save`, `InvRaftNode` (RNNames GF + ss, rnWalTok γ, rnWalTokA/L with walStorRd, rnStopBag/rnWalClosedW/
  rnStopImage/rnDoneEsc without the location, rnApSnap's walSnapRec payload), `InvNodeStart` (rnParts/rnBuilt).
- **Next, in order** (each: edit, `lean-check -a`): the specs `bootstrappedRaft__newRaftNode` (`isWalStorage st γw.wal.h
  γw.ss` replaces `isWalStorage st ∗ ⌜rnStorageOf st ss ∧ walOf st = wal⌝`), `raftNode__onStop` (rnWalTok γ r 1; walMetaIs
  γ.wal.h, walPurgeRight γ.wal.h, walStorRd), `raftNode__stop`, `EtcdServer__applyAll` (payload l.228 → walSnapRec),
  `EtcdServer__applySnapshot` (hstp `storageSnap stp ss` → `isWalStorage (mkOk stp) h ss` resource; payload
  l.173 → walSnapRec over `h`; Release via `walRelease_spec`), snapshot/snapshotIfNeeded; then the proofs:
  NodeStart, newRaftNode, raftNode__start (Save sites: `walSaveRn_spec` now takes `ss`, walStorRd from rnWalTokL,
  error arm → `lg.Fatal` as the Sync error at ~l.660), onStop, stop, StopApi, EtcdServer__run/snapshot,
  ApplyAllSnap, SnapApplyWalk/SnapRO/SnapTake, InvRestart, NewServer(R), StopShutdown, InvRunRes/InvRaftLoop/InvBuild/
  AuthCompRows, the examples' Defs (list: `grep -rlE "rnWalTok|rnStopBag|rnDoneEsc|rnWalClosedW|storage\.walOf|walDirOf|walBaseLb|isWalStorage|rnStopImage|rnStorageOf|storageSnap|rnNewStorageOk" Proof Spec`);
  then F2, P2, merge, full build, tcb (report the proto.SizePb delta for the wal collections), collections,
  interfaces, Links (gen-link with LAKE_OPTS), examples' Go, closed-statement STOP.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a -q FILE`.
- **Pitfalls:** a names-only callee (proto.Size): `wp_start_folded`; a ▷ in a Hoare-triple continuation:
  `iintro %err !> H`; an `iprop(False)` hypothesis: `icases H with %h; exact h.elim`; `simp only [hb, and_self,
  decide_true, ↓reduceIte]` after slice-index tests; gen-init needs `PERENNIAL_DIR=/shared/perennial-6d365ee1a`.

### START HERE (2026-11-19 n, fix 0009 in; InvRaftNode's definitions moved; clients next)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; pin 6d365ee1a, `/shared/tmp/manifest-6d3.json` everywhere.
  Merge the origin merge (pin f551a1b46, manifest-f55) when it lands on lean.
- **Fork fix 0009 (approved by the user 2026-11-19):** commit `d3feef9bc` on branch `goose-lean-walfs3-fp9` of
  `/shared/tmp/wal-fork/etcd` (on `34dea163a`), pushed by the user 2026-11-19; pinned in `etc/goose.py`, examples'
  go.mod/go.sum bumped (`bump-go-mod.sh`), `etc/goose.py --check` (etcd, etcd-wal) passes; WAL Go suite passes but
  `TestWALByteMix` (by design); README 0009, `notes/wal-fsext-fork/0009-*.patch`, the nonissue's Fix.
- **Done (bd06269e62 + this commit):** layer 1 `WAL.Save.spec`: room premise gone, update as
  `⌜saveBatchBytes Mr es ≤ maxSaveBatch⌝ -∗ AU`, refused arm (share back); `WalPbIn.SizeLaw` (+ `walRaftP_size`,
  `walSrvP_size`, in `WalPbLaws`); `wal.walInit` + gen-init (MaxSaveBatchBytes, ErrSaveBatchTooLarge); storage Save;
  WalApi's Save law error arm (share, token, AU back); `walSave_law` (split on the size); `isWalStorage_intro`;
  `rnNewStorageOk_holds`; WalTester `member__save`; InvRaftNode definitions (questions.md, forms of 2026-11-19 0009).
  Check state of each: see the checkpoint report / last build log `/shared/tmp/wallink/b-save*.log`.
- **Next, in order:** InvRaftNode's proofs (lean-check); the clients (list:
  `grep -rlE "rnWalTok|rnStopBag|rnDoneEsc|rnWalClosedW|storage\.walOf|walDirOf|walBaseLb|isWalStorage|rnStopImage|rnStorageOf|storageSnap" Proof Spec`:
  ~50 files; raftNode__start's two Save sites: the new error arm → `lg.Fatal`, as the Sync error), F2, P2, merge,
  full build, tcb/collections/interfaces, examples' Go, closed-statement STOP.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a -q FILE`.
- **Pitfalls:** gen-init needs `PERENNIAL_DIR=/shared/perennial-6d365ee1a`; build slots were busy for hours on
  2026-11-19 (full builds queued); handoff m's AU pitfalls still apply.

### START HERE (2026-11-19 m, the four laws proved; STOPPED: the Save batch's room)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean 1b298c1e70 merged (lean had not moved); pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere. Merge the origin merge (pin f551a1b46, manifest-f55) when it lands.
- **Decided (etcd-grove-03, questions.md 2026-11-19):** the forms of session l ACCEPTED; linking `rnNewStorageOk_holds`
  by hand in the examples' adequacy files is fine (list it; tcb-report/gen-link must still see it linked).
- **Done (17eb60285f, + this commit):** `WalRecs`: `walRecs_saveAU`/`saveSnapAU` (commits with the history lb)/
  `releaseAU`/`closeAU` (layer 1's AU from the server's, or from the held records for Close), `walSnapRec_intro`/
  `_synced`, `walSrvHist_snoc_save`/`_snap`. `RnNewStorage`: `walSave_law` (with an explicit `hroom`, see STOP),
  `walSaveSnap_law`, `walRelease_law` (takes `isSnapshotter ss`), `walClose_law`, `walSync_law`; each file
  lean-check 0 errors. `walSaveEntOk`'s bound `< 2^40` (form). nonissues/etcd-wal-save-batch-efbig.md.
- **STOP (open, questions.md):** layer 1's `Save` needs `walCov Sio → saveRoom walSrvMr hs (cs.map walEntW) ≤
  walFreshRoom` (one batch < ~8 TiB); the approved law lacks it and nothing in raft bounds a Ready's total entry
  bytes (etcd sets no `MaxUncommittedEntriesSize`). Options: (a) fork fix in `WAL.Save` (cut between records
  once the tail passes `SegmentSizeBytes`, as 0007 for SaveSnapshot): layer 1 re-proof, a cut inside a `save`
  op (walCutPos/crash model at record granularity), cost unknown, likely >1k lines; (b) fork fix in the raft
  loop (save a Ready's entries in chunks): raftNode.start's proof gains a loop, `walSave` per chunk; (c) an
  error arm for an oversized batch, covered by the raft loop's `lg.Fatal` (AngelicExit): layer 1's error path
  needs the whole share today (`walCov Sio ∨ q = 1`), the raft loop holds a half shared with the apply thread,
  so layer 1's shared handle must survive a failed Save: re-design; (d) a premise of the closed theorems
  (program behavior, not recommended).
- **Next after the decision:** the Save law text in `isWalStorage`/`walSaveSized_spec`/`walSaveRn_spec`;
  `isWalStorage_intro` (in WalApi: the five laws ⊢ the contract; WalApi stays sealed); `rnNewStorageOk_holds`
  (NewStorage: `storageOver`, two `storageRd`; `interface_mkOk_inj` + `go.intoVal_inj`); then handoff l's (2)-(5).
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a -q FILE`.
- **Pitfalls:** an AU transformer: `iauintro; unfold atomic_acc; ihave Hacc := aupd_aacc $$ Hau; unfold atomic_acc;
  imod Hacc; isimp only [texist_cons, …] at Hacc`; an AU from held resources: `iapply fupd_mask_intro
  Iris.Std.LawfulSet.empty_subset`, abort gives back the context; `(walSrvP).hsIn` vs `walHsIn`: state the
  entailment with `have … := walHsIn_of_hsOptC` (iexact does not unfold the projection).

### START HERE (2026-11-19 l, L3 applying the approved statements; stopped for context)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean 1b298c1e70 merged (lean had not moved on 2026-11-19);
  pin 6d365ee1a, `/shared/tmp/manifest-6d3.json` everywhere. Merge the origin merge (pin f551a1b46, manifest-f55) when it lands.
- **Approved (user 2026-11-19 via etcd-grove-03; questions.md):** l3-statements §1-§5, §6, §7 (890 → 888), F2 (a)
  (STOP if F2 needs trusted text or a network assumption beyond "every member runs this code"); §1 forms ACCEPTED.
- **Done (d4a9911718 + this commit; each file lean-check 0 errors):** `WalRecs` (walRecs/walFiles carry `d.sized = true`;
  `storage.walOpen` carries `walLenLb h.w h.dir 0` for Sync; its section takes `wal.Assumptions`, the package
  variable dropped); `InvWal` (`WalNames GF` with `h : WalH GF` for `loc`; `rnDurInv cl ν (w : WalH GF)`; AUs at
  `WalFs.walAuMask`, `rnDurN_sub_walAuMask`; after `iinv` in an AU: `all_goals first | exact rnDurN_sub_walAuMask | skip`);
  `WalApi` (`isWalStorage st h ss`: Save/SaveSnap/Sync/Release/Close laws; `walStorRd st h` reader token;
  `walSaveEntOk`; helper specs `walSaveSized_spec`/`walSaveRn_spec`/`walSaveSnap_spec`/`walSync_spec`/`walRelease_spec`/
  `walClose_spec`; `walOpened h …`; slots `wal.bootOk`/`wal.restartOk` = `∃ h, ⌜h.w = w⌝ ∗ walOpened h … ∗ walPurgeRight h`,
  their `_start` laws give `∃ h ν, ⌜h.w = w⌝ ∗ rnDurInv cl ν h ∗ …`; `rnNewStorageOk` moved here from InvNodeStart,
  over `h`, post `isWalStorage st h ss ∗ walStorRd st h ∗ walStorRd st h`); `InvOpen` (opaques walReady/walSaveOk/
  walCloseOk/walOf/walCreateOk/storageSnap/releaseOk gone; `diskOk := dbOpensOk ∧ snapOpensOk`); `rnStorageOf` gone
  (its snapshotter is `isWalStorage`'s `ss`); new `etcdserver/RnNewStorage.lean`: `walStorSpecs h`, `walSync_law` proved.
- **Forms decided (to report at the checkpoint):** `isWalStorage` takes `ss` (folds `rnStorageOf`/`storageSnap`);
  reader tokens `walStorRd` in Save/SaveSnap/Sync/Release laws (NewStorage gives two; `storageRd` cannot be in a
  persistent contract); `walSaveEntOk` spells `walEntWOk (walEntW c)` as walEntInW's facts (ufWire, 0 < size < 2^48);
  Release's index fact as `⌜m.Index' = md.Index'⌝ -∗`; `d.sized = true` in walRecs/walFiles; `walLenLb … 0` in walOpen;
  `WalNames`/(next) `RNNames` take `GF`; slots existential in `h` with `h.w = w`; rnNewStorageOk in WalApi.
- **Next, in order:** (1) `RnNewStorage.lean`: the Save, SaveSnap, Release, Close laws (each: AU over `walRecs h` →
  layer 1's AU over `walDiskAt h.dir`: `iauintro; unfold atomic_acc; ihave Hacc := aupd_aacc $$ Hau; imod Hacc` as in
  `WalTester/.../wal/SnapAu.lean` and `durable/Inv.lean:durInv_readAU`; update `monoListAuthOwn h.γh` in the commit;
  SaveSnap's `walSnapRec` from layer 2's `walSyncedLb` + the lb; Close: `walRead_of_fold` for `walFiles`), then
  `rnNewStorageOk_holds (wpNew) (hS : ∀ h, walStorSpecs h) : isPkgInit storage ⊢ rnNewStorageOk` (NewStorage gives
  `storageOver`, two `storageRd`; `p @!! T @!! m` is `#(methods T m #p)`; `interface_mkOk_inj` + `go.intoVal_inj`);
  how the examples get it (Link/Adequacy instantiation) is open. (2) `InvRaftNode`: `RNNames GF` (field types reach
  `WalNames GF`), `storage.walOf st` → `γ.wal.h`; rnWalTok/rnWalTokA/rnWalTokL carry `walStorRd` (loop: in rnWalTokL;
  apply: in rnWalTokA); `rnApSnap`'s payload `walBaseLb γ.wal.loc i` → `∃ j m, walSnapRec γ.wal.h j m ∗ ⌜m.Index' = …⌝`.
  (3) clients in import order (`etc/importers.py`): InvNodeStart, NodeStart, newRaftNode, raftNode__start/onStop/stop,
  StopApi, EtcdServer__snapshot (Release via `walRelease_spec`, AU from rnDurInv with `ν.app`), applySnapshot,
  SnapApplyWalk/SnapRO/SnapTake (`storageSnap` hypotheses → `isWalStorage`), InvRestart, examples' Defs.
  (4) F2 discharge (raft ConfState() canonical; MsgSnap metadata canonical). (5) P2 slots/area, examples' Go, builds,
  tcb/collections/interfaces, closed-statement STOP.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a -q FILE`.
- **Pitfalls:** `iinv` leaves an unsolved mask side goal first when the mask is `walAuMask`; `WalH` needs the instances
  `letI := h.ext; h.semOk; h.has; h.W; h.inj; haveI := h.sat` before a layer-1/2 spec; questions.md is gitignored (local).

### START HERE (2026-11-18 k, L3 started: vocabulary + Release in place; STOP: server-statement stop)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean 1b298c1e70 (fmt soundness) merged (61f263bef2: Close's
  unnamed arm gained `fmtErrorOk`/`fmtErrorOkOrNil`, cleanupWAL/RenameAny resolved); pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere (also `LAKE_OPTS` for `etc/gen-link.py`), `.lake/package-overrides.json` = a copy.
  The origin merge (pin f551a1b46, manifest-f55) is still to come: merge it when it lands on lean.
- **Decided (etcd-grove-03, questions.md 2026-11-18):** step 3, fixes 0007/0008, Create at `P` ACCEPTED; meaning changes
  to the server-statement stop.
- **Done (this commit, WIP):** `St/WalRecs.lean` rewritten over layer 1 (`WalA`, `WalH`, `storage.walOpen` moved from
  `InvOpen`, `walRecs`/`walBaseLb`/`walSnapRec`/`walFiles`/`walPurgeRight`/`walMetaIs` defined, laws re-proved; the axiom
  `walFiles` and the opaques `walRecGName`/`walBaseGName`/`walDirOf`/`walMetaRaw`/`walGName` gone);
  `storage.storage.Release.spec` := ReleaseNext's statement, its proof = `wp_proofNext` renamed, the axiom gone,
  `ReleaseNext.lean` deleted. **The branch does not build past these two** (WalApi and the server clients use the old
  vocabulary) until the statements are approved and applied. The wal Link must be regenerated after a build
  (gen-link reads the build: the committed one is pre-merge).
- **STOP:** `notes/wal-link-l3-statements.md` (exact old → new: vocabulary, isWalStorage's five laws, Release, rnNewStorageOk,
  diskOk, step 3's meaning changes, tcb delta, decisions incl. F2).
- **Next after the go:** apply §2-§5 in WalApi/InvOpen/InvNodeStart; prove rnNewStorageOk from NewStorage + the storage specs
  (instances from `h`); `walRecs_open`/`walRecs_save`/`walRecs_saveSnap` (AU from the server's AU); re-prove the clients
  (`raftNode__start`, `raftNode__onStop`, `EtcdServer__snapshot`, `applySnapshot`, `InvWal`, `InvRaftNode`, `InvRestart`,
  StopApi), the slots, the area allocation (P2), the examples' Go (absolute dirs, `--wal-dir`), then the closed-statement stop.
- **Check/Build:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a FILE`;
  `LEAN_NUM_THREADS=4 /shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build [TARGET]` with
  run_in_background (slots were busy for hours on 2026-11-18).
- **Pitfalls:** History i; `ihave #H := lemma $$ Ha` keeps `Ha` when the result is persistent (monoList lb).

### START HERE (2026-11-18 j, step 3 done, full build green; L3 next (not started); stopped for context)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean fb68edfec8 merged; pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere (also as `LAKE_OPTS` for `etc/gen-link.py`, which finds Perennial's
  sources through it), `.lake/package-overrides.json` = a copy of it.
- **Decided (etcd-grove-03, questions.md 2026-11-18):** `walCutPos` widened; Create's Seek law/fp premises; fork
  fix 0008 approved with 0007; the user pushed `goose-lean-walfs3-fp` (`34dea163a`); the examples' go.mod/go.sum
  moved to it (44be2fb320, `notes/wal-fsext-fork/bump-go-mod.sh`); `etc/goose.py --check` (etcd, etcd-wal) passes.
- **Done (6cc3f71187, eb86d5ca41):** see History i. Full default build green (21789 jobs,
  `/shared/tmp/wallink/full5.log`); the six `etc/api` interfaces unchanged; TCB check matches the baseline (891 axioms, 4 sorries).
- **Next: L3** (scope §3.5, §1 #3-#6, §3.1-3.3): the handle record `WalH` in
  `Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean` (instances, `Sio` with `walCov`, `W : WalGS`, `R jr r`,
  `w`, `dir`, `γ : WalShN`, the base's ghost name); `walRecs`/`walBaseLb`/`walFiles`/`walPurgeRight`/`walMetaIs`/
  `walDirOf` redefined in place over layer 1 (`WalFs.walDiskAt`, `walPurgeW`, the read bridge); then the
  server-statement stop: exact old → new of `isWalStorage`'s laws (Save: `hardStateAt` → `hsOptC`, F2), SaveSnap
  without the budget, `rnNewStorageOk`, `storage.Release.spec`, `diskOk`, plus the exported-spec meaning changes of
  step 3 (`walCutPos`: Open/openAtIndex/ReadAll/ReleaseLockTo/cut, WalTester's `cutPos`/`nameBound`).
- **Check/Build:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a FILE`;
  `LEAN_NUM_THREADS=4 /shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build [TARGET]`.
  Wait on builds with run_in_background/Monitor, never `pgrep -f` loops (they match themselves).
- **Pitfalls:** History i.

### START HERE (2026-11-18 i, step 3 done (SaveSnapshot re-proved, budget removed); STOPPED: fork fix 0008)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean fb68edfec8 merged; pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere (also `LAKE_OPTS` for `etc/gen-link.py`: it finds Perennial's sources
  through it), `.lake/package-overrides.json` = a copy of it.
- **Decided (etcd-grove-03, questions.md 2026-11-18):** `walCutPos` widened; Create's Seek law/fp premises accepted.
- **Done:** 6cc3f71187 + eb86d5ca41: `walCutPos` third case (snapshot record), ref.go `cutPos`, etcd-wal retranslated,
  lemmas; budget removed (`walUsed`, `walSnapBudget`, `walSaveRoom`, `snapRoom`, `walUsedAfterSave`, AU transformers,
  `WalShN.γu`; `walHdl` = the fresh-room handle, no γ); `SaveSnapshot` re-proved: shared arm = Save's tail (Seek,
  sync/cut; `walHandleIn_fp`, `walCutPos_snap`; the four offset lemmas moved to CalleeCov), pre arm with
  `walPreSeekOk` (Spec WAL__SaveSnapshotPre), `SegmentSizeBytes ↦□`, `fp ↦ null` (Create: `os.fileWI_preSeekOk`);
  Create takes `SaveSnapshot.spec` at its `P` (was `walPbNone`: cut's laws at `walPbNone` would be false
  hypotheses); storage Save/SaveSnap specs without the budget; WalTester members; Links regenerated.
  Targeted build of the WAL/WalTester/storage proofs green (b7a); full build: `/shared/tmp/wallink/full5.log`.
- **STOP (for etcd-grove-03): fork fix 0008** (`34dea163a`, branch `goose-lean-walfs3-fp` on `f01ae14c9`, local):
  0007 alone made `Create` panic (nil `w.fp` in `cut`) when its first segment passes `SegmentSizeBytes`
  (metadata ≥ ~64 MB; reproduced); 0008: `curOff < SegmentSizeBytes || w.fp == nil` → sync. Pinned and
  translated; README 0008; `notes/wal-fsext-fork/bump-go-mod.sh` for after the push (push `goose-lean-walfs3-fp`,
  which contains 0007). Alternative: keep 0007 alone and give `Create` a metadata bound (< 2^25) premise.
- **Next after the decision:** L3 (scope §3.5): `WalH` in `St/WalRecs.lean`, vocabulary in place, the
  server-statement stop (old → new, incl. the exported-spec meaning changes listed in the report).
- **Check/Build:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a FILE`;
  `LEAN_NUM_THREADS=4 /shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build [TARGET]`.
- **Pitfalls:** `generalize … at H` only takes Lean hypotheses (an IPM one is in the goal: omit `at`); goose turns
  `a || b` into nested ifs (`rw [decide_eq_false h]` per test); `wp_take_receipt` before `wp_auto` consumes the
  method resolve; `walHandleIn_win` keeps the record (close `cut`'s `h'` directly).

### START HERE (2026-11-18 h, fork fix 0007 made and translated; STOPPED before re-proving: walCutPos must widen)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean fb68edfec8 merged; pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere, `.lake/package-overrides.json` = a copy of it.
- **Approved by the user (2026-11-18, via etcd-grove-03):** fork fix 0007, `SaveSnapshot` cuts as `Save` does.
- **Done (this commit):** fork commit `f01ae14c9` (branch `goose-lean-walfs3` in `/shared/tmp/wal-fork/etcd`, on
  `8c28a4296`; NOT PUSHED: **the user must push it before landing**, then the examples' `go.mod`/`go.sum`
  (examples/, examples/k8s/{etcd3,compactor}, examples/axiomcx/incomingof-real) move to its pseudo-version;
  until then `etc/goose.py --check` fails); `TestSaveSnapshotCuts` fails before, passes after; the WAL suite
  (GOWORK=off, go1.27.3) passes but for `TestWALByteMix` (fails by design, as before 0007). `etc/goose.py` pins it; retranslated
  (`--project etcd --src etcd=/shared/tmp/wal-fork/etcd`): only `Code/.../storage/wal.lean`'s `SaveSnapshot`.
  **The branch does not build** at `WAL__SaveSnapshot.lean` (its code changed) until step 3.
- **STOP (for etcd-grove-03): `walCutPos` must admit a cut right after a snapshot record.** The cut's spec
  takes `walCutPos (H.map toM) |H|` (a file starts only at 0 or after a writing `Save`); after the fix a file
  can start right after a snapshot record. `walCutPos` (storage/WalDisk.lean) is the vocabulary of
  `walNameBound` → `walOpenPos`/`walReleasePos`, i.e. of `Open.spec`, `ReleaseLockTo.spec`, `ReadAll.spec`
  (wal-fsext exported results), and the tester's Go oracle mirrors it (`examples/etcd/wal/ref.go` `cutPos`,
  `tCutPos_abs`). Proposed: `walCutPos H b := b = 0 ∨ (∃ h es, H[b-1]? = save h es ∧ ¬ empty) ∨ ∃ m, H[b-1]? =
  snap m`; `ref.go`'s `cutPos` returns `o.snap || …`; retranslate `etcd-wal`. Meaning: Open/ReleaseLockTo's
  "locked from" positions may move later only past a cut after a snapshot record of index below the target
  (what the code now does; the name bound still holds: the record raised `snapi`). Cost ~100-200 lines
  (pass-through uses; `walCutPos_of_take`, `walCutPos_le/snoc`, `tCutPos_abs` destruct it).
- **Next after the decision (step 3):** SaveSnapshot's shared arm: Seek + `sync`/`cut` as Save's tail
  (`walCov_cut`, `save_off_toInt`, `save_hif`, `save_pc_bound`); the pre arm (Create's call): its writer is
  generic (`io.writerStream`), so it needs a Seek law on the writer (offset = `|out|`) and the offset below
  `SegmentSizeBytes` (Create's segment is far below it; `lim < 2^47` is not enough), plus the global's `↦□`;
  then remove `walUsed`/`walSnapBudget`/`walSaveRoom`/`snapRoom`/`walUsedAfterSave`/`WalShN.γu` (walHdl =
  walHdlF's form), Save's room premise over `walFreshRoom`, the AU transformers, storage Save/SaveSnap specs,
  WalTester member__save/saveSnap; then L3 (scope §3.5).
- **Check/Build:** as in History g.

### START HERE (2026-11-18 g, per-area WalGS done; L3 STOPPED at a blocker: the snapshot room budget)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean fb68edfec8 merged; pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere, `.lake/package-overrides.json` = a copy of it.
- **Decided (etcd-grove-03, questions.md 2026-11-18):** the option (C) forms ACCEPTED; next per-area WalGS, then L3.
- **Done:** 3f2e245eb1 one `WalGS` per area: `walBoot0` takes the claims held (`Js`, `hjr : jr ∈ Js`; it was the
  boot tree's list), new `walBoot0s` (each area of a list `As` in turn: its own `WalGS`, lock and crash tokens,
  `walAreaOk`/`walAreaRes`; back the claims no area took); WalTester's `Boot0` passes the tree's list. Nothing
  else was global: `WalGS` already came per `walBoot0` call (`absDisk_local_init`); `walN` is shared but no proof
  opens two areas' invariants at once. lean-check 0 errors (Boot0, WalTester Boot0). Multi-area crash (one
  `crashRest` per crash) is L6's.
- **BLOCKER (STOP, for etcd-grove-03):** L1a's (A) SaveSnapshot budget (`walUsed γ u`, `u + snapRoom ≤ 2^42`
  since the last writing `Save`) is not dischargeable by the server: the apply thread saves a snapshot record per
  applied batch (`appliedi - diskSnapshotIndex > SnapshotCount`), raft hands a commit backlog out over many
  `Ready`s with empty hard state and entries (whose `Save` writes nothing), so the records between two writing
  `Save`s are bounded only by the commit backlog, which nothing bounds (raft's room: `2^61`). The Go code really
  hits `EFBIG` there (16 TiB tail, `lg.Panic`): `nonissues/etcd-wal-savesnapshot-tail-efbig.md`. Options in
  questions.md (2026-11-18, OPEN "the snapshot room budget").
- **Next after the decision:** L3 (scope §3.5): the handle record `WalH` (instances, `Sio` with `walCov`, `W`,
  `R jr r`, `w`, `dir`, `γ : WalShN`, the base's ghost name) in `St/WalRecs.lean`; the vocabulary redefined in place
  over it; the server-statement stop with exact old → new.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a FILE`
  (`--fast` can hide errors: re-check without it, or build). **Build:**
  `LEAN_NUM_THREADS=4 /shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build [TARGET]`.
- **Pitfalls:** previous START HERE (History, f).

### START HERE (2026-11-18 f, step B: option (C) done; WAL + WalTester + durable build; lean merged; full build)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean fb68edfec8 (origin's big merge) merged (898bd6d54d);
  pin still 6d365ee1a, `/shared/tmp/manifest-6d3.json` everywhere, `.lake/package-overrides.json` = a copy of it.
- **Decided (etcd-grove-03, questions.md 2026-11-18):** option (b) and the key forms ACCEPTED; option (C) for handle roots.
- **Done (d68da68c02..9242b35b18):** (C): `walPipeH`/`walDirH`/`walCloseLeft` carry `⌜R = W.roots⌝`; `walAreaOk` carries
  `osAboveInv`; fileutil TouchDirAll/TouchDirAllDir/CreateDirAllTmp, os MkdirAll(Dir)/RemoveAll*/RemoveAllFrom keyed; WAL
  dir key = area root key via `osPathS_callKey` (Open, openAtIndex, Repair, openLast, VSE, cleanupWAL, renameWAL, Create);
  `storage.Close.spec` keyed; WalTester `tPerm` (forms list: questions.md 2026-11-18 "option (C) and the rest").
  `lake build` of the WAL Link + WalTester wal/durable Links green (b5.log) before the merge.
- **Verified:** full default build green after the merge (21789 jobs, `/shared/tmp/wallink/full4.log`, with
  RenameAbsentSrc fixed); `etc/tcb-report.py --check` matches the baseline (891 axioms, 4 sorries); the six
  `etc/api` interfaces unchanged (`gen-interface.py --check`).
- **Next, in order:** the
  per-area ghost instances (one `WalGS` per area; `walUnlockedTok` per area); then L3 (scope §3.5: server-statement
  stop with old → new incl. Save's `hardStateAt` → `hsOptC` and F2; then the examples' Go to absolute dirs +
  `--wal-dir`; STOP with the exact old → new closed statements for the user).
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a FILE`
  (`--fast` can report 0 errors on an incremental re-check that a build then rejects: re-check without it, or build).
  **Build:** `LEAN_NUM_THREADS=4 /shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build [TARGET]`.
  `/shared/tmp/wallink/scripts/chkloop.sh LIST OUT` lean-checks a list of files in order (summary OUT, errors OUT.err).
- **Pitfalls:** key mismatch dir vs root: get `hkc` from `osPathS_callKey R r _ jr $$ Hp`, then `rw [← hkd]` on the goal
  and `rw [hkd]` in an r-keyed callee's framing subgoal; `osCallPerm_child`/`_unchild` around a call on `child d b`;
  sealed W.roots keys: `walPerm_toW/ofW hWR`; `subst Rp'` may pick the wrong equation (use `subst hRp` by name);
  `e.orFile.d` vs `e.orDir` is defeq but not reducible: `osCallPerm_congr qc (show … from rfl)`.


### START HERE (2026-11-18 e, step B: option (b) done; os + fileutil converted; WAL started; STOP for the handle-roots form)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean 49bd7924e6 merged; pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere, `.lake/package-overrides.json` = a copy of it.
- **Decided (etcd-grove-03, questions.md 2026-11-18):** step B forms ACCEPTED; option (b) with a SEPARATE invariant.
- **Done (4ec0ae0ea9, this commit):** `osAboveInv := inv osAbN (∃ q, osCallPerm [] q)` (TreeSharedRes; docstring: no proof
  needs the whole of key `[]`); `wp_osShare` gives it beside `osCallPerms R` (now every root's key, `delete [] permMap`);
  `osAboveInv_take`, `osSharedInv_rootsOk`, `wp_osCallBeginAboveS` (TreeShared), `rootsAbove_not_under`, `callKey_above`
  (TreeSharedOut). Above-root specs: `os.Stat.specAboveRoot` no permission (no call), `os.OpenFile/Open.wp_aboveS`,
  `fileutil.OpenDir/syncDir.specAboveRoot` take `osAboveInv` (no share back); `wp_statAnc`/`wp_syncDirAnc` keyed by the
  root (`callKey R (joinPath [] rcs)`, `callKey_joinPath`); TouchDirAll(.specDir)/CreateDirAll(.specTmp) take `osAboveInv`.
  Proof/os RemoveAllDir, RenameS (d' key via `callKey_of_sameRoot`) fixed. lean-check 0 errors: Fs TreeShared(+Switch),
  Proof/os StatS/RemoveAllDir/RenameS/NsAbove/StatAbove, fileutil CheckDirPermission/ReadDir/OpenDir/syncDir/IsDirWriteable(File)/
  ReadDirAbsent/OpenDirOk/Exist/FsyncS/TouchLemmas. Not yet checked: fileutil TouchDirAll/TouchDirAllDir/CreateDirAllTmp
  (pass `#Hab` to wp_syncDirAnc), the other Proof/os files since step B's script (os-check1.log said 0 errors).
- **WAL (started):** `WalGS.roots` (Ghost; `walGhost_init R` gives `⌜W.roots = R⌝`); `walInv := ⌜W.roots = R⌝ ∗ inv ...`
  (`walInv_roots`, `walPerm_toW/ofW` in Inv; `walInv_alloc` takes `hWR`; `walStart_boot0`/`walInv_crash` give it;
  `walBootCrash` takes `hWR`); `walAreaOk_roots`. Keys by `/shared/tmp/wallink/scripts/walkey.py` (first `osPathS R D` ->
  `callKey R D`; else R+dir, R+r; sealed defs without R: `callKey W.roots dir`); keyed helpers (`walhelpers.py`).
  Checked: Ghost..Inv..Crash, Boot0, BootCrash, Pipe, PipeLemmas, ReadAllFail. **Failing:** WAL__CloseOpening (merge of the
  pipeline's quarter `callKey Rp dir` with the client's `callKey R dir`), WAL__CloseU, the rest unchecked.
- **STOP: the handle's roots.** The handle predicates quantify their own roots (`walDirH`'s `∃ R` with `osSharedInv R`,
  `walPipeH`'s `∃ R` (`pp` default True), `CloseLeft`'s `∃ R`, `walOpenWFU`'s `Rp`); at Close the quarters must merge under one
  key, so `R_h = R` is needed and nothing gives it. Options in the report (questions.md 2026-11-18, OPEN).
- **Next after the decision:** the WAL's 55 files (lean-check in `/shared/tmp/wallink/walorder.txt` order), WalTester (TBoot gets
  `osAboveInv` + the root's key; `walBootCrash`'s `hWR` from `walInv_crash`), walfs, merge lean, full build, per-area WalGS, L3.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -q -a
  --fast FILE`. **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build` (slots were busy
  all session).
- **Pitfalls:** `osCallPerm_split` now takes the key first; `wp_osCallBeginS R _ q` unifies `p` with the held key's path:
  convert first (`osCallPerm_child`/`_unchild`, `osCallPerm_congr q h`); `walPerm_toW hWR d q` converts R-keys to W.roots-keys;
  a `rw [hWR]` on the IPM goal fails when W.roots only appears after an `iapply`.


### START HERE (2026-11-18 d, stage 2 step B: per-key permission in the fs library; os clients WIP; STOP for a decision)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; lean 49bd7924e6 merged (9d28ebb29f); pin 6d365ee1a,
  `/shared/tmp/manifest-6d3.json` everywhere, `.lake/package-overrides.json` = a copy of it.
- **Done (step A, accepted):** b93dd9be92 (CallsK per key), full build green at 8c66a9bb3d.
- **Done (step B, this WIP commit; the fs library `GooseLang/Ext/Fs/*` builds, checked by lean-check through
  `Proof/os/SharedExt`):** `γperm : GoString ↦ Unit`; `osCallPerm r q` (TreeSharedRes); legacy holds
  `gAuth γperm ∅` (no element: `legacy_perm_excl` by `gAuth_lookup`); `callResS hL R Γc` keyed by
  `callKey R x.1.2`; `permMap R` (`[]` and each root), `osCallPerms R`, `perm_alloc`; `wp_osShare` gives
  `osCallPerms R`, `osCallPerms_root` takes one root's whole; CallBegin(Guard) take `osCallPerm (callKey R p) q`;
  `callResS_excl`/`callsRes_facts`/`sole_of`/`wholeG_facts` per key; `hsole` (hprog/hpost/hworld) per key
  (`callKey R s'.2 = callKey R pc → k' = k`), `renameStep_err`'s `hex` takes `SameRoot (child d bs) s'.2`
  (`callKey_of_sameRoot`); `osCallPermG r q gd`; `wp_logStepS*`/`wp_callEndS` give back `callKey R pc`; every
  step spec on a name of a spine directory `d` gives back `osCallPerm (callKey R d) q` (`osCallPerm_unchild`);
  OpenDir/OpenAbove/LstatDirGuard give back `callKey R p`. Moved to TreeSharedRes: `isUnder_prefix`,
  `root_of_isUnder`, `callKey_eq`; new: `callKey_of_sameRoot`, `callKey_joinPath`, `permMap_lookup`,
  `osPathS_callKey`, `osCallPerm_congr`, `osCallPerm_child`/`_unchild`.
- **Clients (WIP, not building yet):** `Spec/os`, `Proof/os`, fileutil `Spec`/`Proof` rewritten by
  `/shared/tmp/wallink/scripts/keyperm.py` (key = `callKey R D`, `D` the first `osPathS R D` of the declaration),
  `unchild.py` (Proof/os fs-level wrappers), `childbegin.py` (+ hand-placed `osCallPerm_child` before each
  `wp_osCallBeginS` on `child d b`). lean-check status: `/shared/tmp/wallink/os-check1.log` (most Proof/os
  files 0 errors; open: MkdirAllParts (edited after the check: `callKey_joinPath` conversions), RemoveAllDir
  l.345-357, StatS l.135/182, fileutil CreateDirAll, RemoveAll*, RenameS (d' key)). WAL, WalTester, walfs:
  not started.
- **STOP: decision needed (keys of calls above the roots).** `fileutil.TouchDirAll`'s proof (`wp_statAnc`,
  `wp_syncDirAnc`, `wp_existAnc`, TouchLemmas/TouchDirAll*) stats/syncs ancestors ABOVE the root
  (`os.Stat.specAboveRoot`, `syncDir.specAboveRoot`, `OpenDir.specAboveRoot`, `NsAbove`) with the same
  `osCallPerm qc` it uses in the root. With keys, an above-root call's key is `[]`, so a client holding only its
  root's key cannot make it. Options: (a) above-root specs take a share of key `[]`
  (`osCallPerm [] qa`), threaded through TouchDirAll/CreateDirAll/wal.Create up to the boot (ripples into the
  WAL's Create spec); (b) recommended: the `[]` key's permission lives in a dispenser invariant
  (`∃ q, osCallPerm [] q`, halved on each take) folded into `osSharedInv` (or a persistent `osAboveInv` the
  switch gives beside it); an above-root `CallBegin` needs no share (takes half of what the dispenser holds; the
  returned share may be dropped): the above-root specs lose their `osCallPerm` (weaker pre), no client above
  them changes. Cost of (b): ~32 `unfold osSharedInv` sites (fs library, 4 WAL Create files, PathKindS) if folded,
  or one persistent premise on the above-root specs if separate.
- **Next after the decision:** finish Proof/os + fileutil; then WAL (32 Proof + 23 Spec files: its handle
  predicates `walOpeningF`, `walReadH`, ... hold `osCallPerm` without `R`: a key parameter or `callKey R dir` with
  `R` in the handle record, to design with the per-area WalGS), WalTester (16), walfs; full build; then per-area
  WalGS, L3 (as before).
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -q -a
  --fast FILE` (it rebuilds changed imports with lake: a changed `TreeSharedRes` costs minutes). **Build:**
  `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build`.
- **Pitfalls:** `wp_osCallBeginS R _ q` unifies `p` with the held key's path: convert first
  (`icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩`); in a direct step proof (no
  `wp_logStepS`), the `[Hq]` subgoal needs `rw [← hkd b, ← hR]` (`osPathS_callKey` at the start);
  `obtain ⟨hR, rfl⟩ := hVs` gives `hR : st.fs.roots = R` (Out substs it).


### START HERE (2026-11-18 c, stage 2 step A done: per-key call coherence under the global permission)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; **lean merged** (9bc323ff9d, lean b0bb9df7c3, Perennial pin
  6d365ee1a): use `/shared/tmp/manifest-6d3.json` everywhere; `.lake/package-overrides.json` = a copy of it. Full
  default build green after the merge (20488 jobs).
- **Decided (etcd-grove-03, questions.md 2026-11-18):** the per-root crash theorem and its forms ACCEPTED.
- **Done:** 0da9fec13d the root clause in `wp_logStepSWG`'s `htree` (5 wrappers, 9 client sites; `rootClause_one/two`,
  `root_of_isUnder`, `reachFrom_of_lookup`); full default build green at it. **This commit (step A):** `callKey R p`
  (Ghost; `callKey_eq` in TreeSharedLog); `CallsK st s0 ρ Γc Γg` (Ghost: `whole`/`after`/`pair` per key, tags by
  `tagOf ρ`), `TreeCohS.rc : ∃ ρ, RootCoh st s0 ρ ∧ CallsK st s0 ρ Γc Γg`, the global `whole`/`after`/`pair` fields
  removed from `TreeCohS`; `treeCohS_log`'s premises per key (`hdirK` replaces `hdirS`; `hexcl`/`hval` take the
  same-key hypotheses; `hρ` gives `ρ' o.dir = callKey R pc`), DirOpExcl's new-entry clause from `hdirK`;
  `WholeG R pc q s0 gd` (a guard must be of the call's key); `wholeG_facts` gives "no entry of the key from `s0`";
  `wp_osMkdirSG'`/`wp_osRmdirSG'` (and TreeShared's wrappers) take `hkg : callKey R pg = callKey R (child d b)`
  (RemoveAllDir: `rfl`). The permission itself is still GLOBAL (one `γperm` element). Fs library + Proof/os
  RemoveAllDir/UnlinkN build (1866 jobs); full default build green at b93dd9be92 (20488 jobs, manifest-6d3).
- **Next, in order:** stage 2 step B: split the permission per key (design (2) and (4) below; (3) is done as
  `CallsK`): `osCallPerm r q`, `callResS` keyed, `sole_of`/`callResS_excl`/`callsRes_facts`/`wholeG_facts` per key,
  `hsole` (hprog's "q = 1 → only call") per key, then the ~144 `osCallPerm` client files,
  one `WalGS` per area, then L3 (task list: `questions.md` 2026-11-18, the coordinator's brief).
- **Stage 2 design** (form decisions to record at the checkpoint):
  (1) `callKey (R : Roots) (p : GoString) : GoString` := the root `r` with `IsUnder r p` (`Classical.choose`), else
  `[]`; `callKey_eq : RootsOk R → rj ∈ R → IsUnder rj.1 p → callKey R p = rj.1` (by `root_of_isUnder`).
  (2) `γperm` a ghost map `GoString → Unit`: `osCallPerm r q := gElem γperm r (own q) ()`; `callResS hL R Γc :=
  [∗map] t ↦ x ∈ Γc, gElem γperm (callKey R x.1.2) (own x.2) ()`; legacy: `gAuth γperm ∅`; shared: an existential
  auth; the switch (`cohS_switch`/TreeSharedSwitch) inserts one whole per root and one for `[]`; `fs_start` hands
  them out (`[∗list] r ∈ R.map (·.1) ++ [[]], osCallPerm r 1`).
  (3) `whole`/`after`/`pair` move from `TreeCohS` into `RootCoh` (they need its ρ), per key `K = callKey R x.1.2`:
  whole: `x.2 = 1 → ∀ y ≥ x.1.1, y ≥ s0, tagOf ρ (log y) ≠ K`; after: `(IsDirOp ∧ tag = K) ∨ y < s0 → y < x.1.1`;
  pair: same key, `x.2 + g.2 = 1`, `g.1.1 ≤ x.1.1` → no entry of tag K from `x.1.1` on. Plus `RootTags.ops`' tag of a
  logged entry = the logging call's key: from the root clause (`ρ o.dir = rj.1 = callKey R pc`). `DirOpExcl` per root
  then follows at a dir op from whole (before) and every in-flight call's `after` (later).
  (4) `sole_of`/`callResS_excl`/`callsRes_facts`/`wholeG_facts` compare only calls of the same key (validity of
  `gElem γperm K`); `hexcl`/`hval` premises of `treeCohS_log` become per key.
  Files touching `callResS`/`legacyHolds`: Ghost, CrashTok, TreeSharedLog/Step/Switch/Guard/Create/DirFd/OpenDir/
  OpenFileN/Out/Trunc; `whole/after/pair` uses: TreeSharedStep, Switch, OpenDir, DirFd, Log.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -q -a
  --fast FILE`. **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build`.
- **Pitfalls:** `cases o` inside a big proof fails (o in many hypotheses): state a standalone lemma (`dir_mem_slots`);
  `by_contra` is not available in these files (`Classical.byContradiction`); a state built by
  `callBegin`/`delDfd`/`setDfd`/`metaEnd` is not syntactically `st` in `RootCoh`: pass `hc.rc.elim (fun ρ h => ⟨ρ,
  h.congr rfl rfl rfl⟩)`.


### START HERE (2026-11-18, per-root crash theorem: pure part done; fs library NOT building at this head)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`
  (switch both to `manifest-6d3.json` after merging lean once the 6d365ee1a pin bump lands; not landed on 2026-11-18).
- **Decided (etcd-grove-03, questions.md 2026-11-18):** phase A accepted; the per-root crash-theorem rework approved
  (part of L4). `closed_cut`/`machineCrash_initS` checked internal (Fs extension only; no interface, Results or tcb root).
- **Done (this commit, WIP):** `TreeCut.lean`: `MetaOp.dir`, `tagOf ρ`, `ReachFrom`, `RootTags ρ R T0 log s0` (roots,
  ents for t >= s0, ops for x >= s0), `DirOpExcl ρ log s0` per root (legacy clause global; a dir op excludes only its
  root's entries). `TreeCutProof.lean` (968 -> ~1060 lines): `closed_cut` restated IN PLACE (takes `hρ : RootTags`; 4th
  conclusion now "each kept directory is in some prefix tree"), reproved per root (`cut_base_r`, `run_dirs_r`,
  `kept_slot_r`, `kept_keys_below`/`_r`, `kept_inj` from s0, `treeWf_merge`, `reach_restrict`; case "nothing kept past
  s0" = a prefix); `rootTags_exists` (a tree's tags, for the switch). Checked with the kernel (lean-check, no --fast).
  `Ghost.lean`: `RootCoh st s0 ρ` (tags, dox, wkeys: written dirs are dirs of the tree now); `TreeCohS.dox` replaced IN
  PLACE by `rc : ∃ ρ, RootCoh st s0 ρ` (no new TreeCohS parameter: no icases pattern changes); `TreeCohS.congr` takes
  `hr` (roots). `CrashFiles.machineCrash_initS` over the new `closed_cut` (checked). `TreeSharedSwitch.cohS_switch` takes
  `FsTreeWf` and builds ρ by `rootTags_exists`. `TreeSharedLog.treeCohS_log` keeps `rc` (proved) given three new
  premises: `hw : FsTreeWf st`, `hroots`, and `hρ : ∀ ρ, RootCoh st s1 ρ → ∃ ρ', ρ' = ρ on st.tree ∧ every dir o
  writes has ρ' = ρ' o.dir ∧ every dir o writes is a dir of o.apply st.tree`. Helpers there: `mem_of_entry`,
  `writes_dir`, `prefTree_mono_mem`, `ents_apply`; `mem_apply_of_mem` moved to TreeCutProof.
- **Next, in order:** (1) the one failing site, `TreeSharedLog.lean` ~l.1211 (`wp_logStepSWG`'s call of
  `treeCohS_log`): add to its `htree` premise the clause `∃ rj ∈ R, IsUnder rj.1 pc ∧ ∀ c ∈ cl, ReachFrom st.tree rj.2
  c.1`, build ρ' := `fun j => if j ∈ o.newDirs then ρ o.dir else ρ j` (newDirs ∉ st.tree by htree), get `ρ c.1 = rj.1`
  by `rho_of_reachFrom` (roots + ents at the current tree), slot dirs ∈ claims (`hslots`), `o.dir` a slot dir; thread
  the clause through the 5 wrappers (`wp_logStepSW/SN/S/SNG/SG`) and the 12 client sites (TreeSharedCreate 2,
  CreateN 1, Meta 6, RenameAny 2, `Proof/os/UnlinkN` 1) with a lemma `reachFrom_of_lookup : st.lookup d = some (.dir j)
  → ∃ rj ∈ roots, IsUnder rj.1 d ∧ ReachFrom st.tree rj.2 j` (from `lookup_some` + a `walk` induction as
  `reach_of_walk`) and `IsUnder r d → IsUnder r (child d b)`; cross-directory renames: the two lookups' roots agree by
  `hsr : SameRootR` and root uniqueness of a path (RootsOk: no root under another). (2) full fs build; (3) stage 2: the
  per-key permission (`callKey`, `osCallPerm r q`, `whole`/`after`/`pair` per key inside `RootCoh`, tag = callKey pc
  from the clause above), then the ~145 client files, one WalGS per area, L3.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 -q -a
  --fast FILE`. **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build`.
- **Pitfalls:** a state built by `callBegin`/`delDfd`/`setDfd`/`metaEnd` is not syntactically `st` in `RootCoh`:
  pass `hc.rc.elim (fun ρ h => ⟨ρ, h.congr rfl rfl rfl⟩)`, not `hc.rc`; `writer_tag`/`Writes` from `.inl hsl` needs
  `(j := sl.1) (b := sl.2)`; a `let` bound by `Classical.choose` is opaque to `omega` (ascribe the fact to the let).

### START HERE (2026-11-17, L4 phase A: calls carry their paths; STOP at the per-root cost delta)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`
  (switch both to `manifest-6d3.json` after merging lean once the 6d365ee1a pin bump lands). Coordinator: etcd-grove-03.
- **Done:** L0-L2, L4 trusted text (History). **The configuration-C run is DONE and meets the landing condition** (the user,
  2026-11-17; `notes/wal-link-l4-fsext.md`). **L4 phase A** (this commit): the fs library and its direct clients over the
  new `CallBegin`/`calls`/`Rename` with the **global** permission unchanged: ghost call maps hold `CallV := (Nat ×
  GoString) × Qp` (start, path, fraction); `osCall`/`osCallS`/`osGuardS` carry the path; CallBegin specs take `p`;
  generic steps take the call's path `pc`; `SameRootR` (TreeLemmas) + `sameRoot_of_R`, `sameRoot_child_child`,
  `osPathS_sameRoot` (TreeShared); cross-directory rename specs take `hsr : SameRootR R (child d bs) (child d' bt)`
  (fs legacy + shared, `os.Rename.specFileS(nc)`); the dir-rename clause from the global sole (`Or.inl`). Checked:
  every `GooseLang/Ext/Fs` file, 34 `Proof/os`+`Spec/os` files, walfs `DSTree`/`Boot`/`DirSwap`/`SegLogOps`, `WAL__cut`,
  WalTester `tryWrite` by `lean-check --fast`; then the full default build green (20488 jobs, c6b manifest, 2026-11-18;
  only `InvOpenTest`'s toy rename needed `hsr`). No axiom, `sorry` or trusted text changed by phase A.
- **STOP (cost delta, for etcd-grove-03):** the per-root permission breaks `TreeCohS.dox` (`DirOpExcl`, TreeCut.lean),
  which `closed_cut` (TreeCutProof.lean, 661 lines; the crash theorem `machineCrash_initS`) needs **globally**; today
  it is kept by the whole global permission (`wholeG_facts`: no other logging call in flight at a directory op). With
  a root's whole permission only, a directory op in root A overlaps calls in root B, and `closed_cut`'s 4th conclusion
  (the kept tree's directories are one prefix tree's) is false: A's `mkdir` at index 0 (begun 0), B's `mkdir` at 1
  (begun 0), `S = {1}` is closed, the kept directories match no prefix. Needed: a ghost root tag per log entry
  (maintained in `TreeCohS`), `DirOpExcl` per root, `closed_cut` restated per root (4th conclusion weakened to "each
  kept directory is in some prefix tree": all `machineCrash_initS` uses) and reproved (per-root projection of the log +
  a merge of disjoint replays, or the cut argument per root). Estimate +800-2000 lines of pure Lean, beyond the
  Scope's 1500-3000 for all of L4's Lean. Not started.
- **Next (after the decision):** the per-root split as planned (`callKey`, `osCallPerm r q`, `callResS` keyed by
  `callKey R x.1.2`, the auth `γperm` (legacy `gAuth γperm ∅`, shared an existential auth beside `γc`'s), per-key
  `sole_of`/`callResS_excl`/`callsRes_facts`, `fs_start` one whole per key) together with the per-root cut; then
  `osCallPerm` clients (~145 files), one `WalGS` per area, L3.
- **Optional (not a landing condition):** env switches in `meta_rename_scoped_test.go` (cold dcache by a remount, a
  ~100k-entry B directory) and `examples/osfs/semantics/run-l4-configc.sh`.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 -q -a
  --fast FILE`. **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build` (slots were
  busy for >1 h on 2026-11-17: lean-check first). Scripts used for the mechanical edits: `/shared/tmp/wallink/scripts/`.
- **Pitfalls:** a step's call path must be the step's exact path (`child d b`): pass `_` to `wp_osCallBegin*` and let
  unification find it; `calls_start` now compares pairs (`have hse := calls_start …; simp only [Prod.mk.injEq] at hse`);
  `Rename`'s inversion has one more conjunct (`SameRoot`); `Roots` is not in scope in TreeLemmas (use `List (GoString × Ino)`).


### START HERE (2026-11-17, L4 text applied; fs library NOT yet rebuilt)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`
  (switch both to `manifest-6d3.json` after merging lean once the 6d365ee1a pin bump lands). Coordinator: etcd-grove-03.
- **Done:** L0-L2 (History); b8b64e6e59 L2 trust-base delta; L4 revision 2 APPROVED BY THE USER (2026-11-17) and
  applied in the commit after d117e99f31/f69bce09b3: `Impl.lean` (`calls : GMap Nat (Nat × GoString)`, `CallBegin`
  `v = #p`, steps match `some (start, p)`, `OsState.SameRoot`, `Rename` needs `SameRoot s t` and its directory clause
  `k' = k ∨ ¬ st.SameRoot s p'`, environment clause, docstrings), `os.lean` (11 sites pass their path; Stat/RemoveAll
  docstrings), Go `meta_dir_rename_stuck.go`, `meta_rename_cross_root.go`, `doc.go`, `meta_rename_scoped_test.go`
  (`L4_CROSS_EXPECT=1` asserts a positive count).
- **OPEN OBLIGATION (the user's condition):** no land before the configuration-C run (`notes/wal-link-l4-fsext.md`,
  "Open obligation"); etcd-grove-03 arranges it.
- **State:** the fs library does NOT build at this head: first errors `GooseLang/Ext/Fs/Ghost.lean:505,1167,1172`
  (`TreeCoh.calls`, `TreeCohS.calls/gcalls/cover` over the old `calls : GMap Nat Nat`) and `Tests.lean:720,735,952`
  (the trusted tests of Rename/CallBegin). ~180 `proc.calls` uses in ~25 Fs files, then `Proof/os` (~40 files),
  walfs, layer 1, WalTester.
- **Next (one pass, do not first patch the global permission):** the per-root call permission.
  (1) `callKey roots p` := the root `r` with `IsUnder r p` (unique by `RootsOk`), else `[]`; `SameRoot s p' ↔ callKey s =
  callKey p'` for `s` a `TreeName`. (2) `Γc`/`Γg : GMap Nat (Nat × Qp)` gain the key (`Nat × GoString × Qp`);
  `TreeCoh(S).calls`: `Γc !! t = some x → st.proc.calls !! t = some (x.start, p) ∧ callKey p = x.key` (legacy:
  `(Γc !! t).map start = (calls !! t).map (·.1)`). (3) `γperm` keyed by root (`gElem γperm r (own q) ()`): `osCallPerm r
  q`, `callResS` per key; `sole_of`/`callResS_excl`/`callsRes_facts` per key, giving the new clause. (4) `CallBegin`'s
  specs take the path and a share of `osCallPerm (callKey p)`; `fs_start` gives one whole per root and one for `[]`.
  (5) Rename specs gain `SameRoot s t` (every client renames within one directory and its parent). Then `Proof/os`,
  `Spec/os`, fileutil, layer 1 (`Create`/`cut` over their area's root), WalTester, walfs; then one `WalGS` per area;
  then L3 (plan in the previous START HERE, History).
- **Build the fs library:** `mods=$(ls GooseLang/Ext/Fs/*.lean | sed 's|/|.|g; s|\.lean$||'); LEAN_NUM_THREADS=4
  /shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build $mods` (~10 min when Ghost is reached).
- **Pitfalls:** as in the previous START HERE (gen-link/gen-init Perennial link; goose flags; tcb `--reuse`); semantics
  tests here: `SEMANTICS_C_DIR=/shared/tmp/wallink/l4-c` (no loop devices for `run-models-on-c.sh`).


### START HERE (2026-11-17, L3/L4 start; STOP at L4's trusted text)


- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`.
  Coordinator: etcd-grove-03. Scope §3-§5, §7-§8; `questions.md` (git-ignored, local).
- **Done:** L0-L2 (History). b8b64e6e59 the L2 trust-base delta (approved): `EtcdServer.purgeFile.wp_proof` out of
  `etc/tcb-baseline.txt` and 24 collections; `notes/release-snapdb-held-file.md` status (route closed by T1).
- **L4 trusted text (STOPPED, hard stop (a)):** `notes/wal-link-l4-fsext.md`: `CallBegin` takes its path, `calls`
  records it, each call step names it, `Rename`'s directory stuck clause scoped to the source's and target's roots
  (`OsState.SameRoot`), 11 `os.lean` sites; Go evidence `examples/osfs/semantics/meta_rename_scoped_test.go`
  (passes on this machine's ext4; no loop devices here, so not on a `c_mkfs` image). Not applied to Impl/os.lean.
- **Revision 2 (after the attack's BLOCKER, fix (b) `SameRoot s t`):** the note's "Revision 2"; excluded case
  `TestCrossRootRenameExcluded` (13/2000 here), `meta_rename_cross_root.go` + `doc.go`; configuration-C run open.
- **Next, in order (after the verdict):** apply L4's text (+ `meta_dir_rename_stuck.go`, `doc.go`); the fs library's
  per-root `osCallPerm r q`; layer 1 per-area `WalGS`. L3: planned form, the server's WAL vocabulary over an explicit
  handle record (`w`, `dir`, `WalGS`, `WalShN`, the fs instances as fields), so no server module or `NewServer.spec`
  gains fs instance arguments (they have none today); `walRecs`/`walFiles`/`walOpened`/`isWalStorage` redefined in
  place; `storage.Release.spec` := ReleaseNext's statement, axiom gone; the Save law's `hardStateAt` → `hsOptC`
  (statement stop (b)); F2's conf state (raft's snapshot conf state canonical, else a model wrap).
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial` (`ln -s
  /shared/perennial-c6b39d4f8`, then `rm`); gen-init needs `PERENNIAL_DIR=/shared/perennial-c6b39d4f8`. goose:
  `PATH=/usr/local/go/bin:$PATH etc/goose.py --project etcd --src etcd=/shared/tmp/wallink/etcd --perennial
  /shared/perennial-c6b39d4f8`. tcb: `etc/tcb-report.py --reuse --collection F --check --update` after one full run.
  `run-models-on-c.sh` fails here (no `/dev/loop*`); run semantics tests with `SEMANTICS_C_DIR=/shared/tmp/...`.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.



### START HERE (2026-11-17, L2 done; STOP at the L2 trust-base stop)


- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`.
  Coordinator: etcd-grove-03. Scope §2-§3.5, §7-§8; `questions.md` (F1, F2, bounds, R6, purgeFile decided by etcd-grove-03).
- **Done (L2):** 771d63dd6b storage.toml (accepted). 03d78a9a97 the storage package: `StorageRep.lean` (`storagePw`,
  `storageOver`, `storageRd`, `metaWalC`, `walSnapAt_storageLit`), specs+proofs `NewStorage` (two reader tokens: bounds
  unchanged), `storage.{Save,SaveSnap,Sync,Close}` (= the WAL method's triple + the storage's lock; SaveSnap over
  `metaRoC` with the F2 premise `snapEnc (metaWalC m) = Mr.encSnap m.model`); `ReleaseNext.lean`
  (`storage.storage.Release.wp_proofNext`, used by nothing: F1, becomes the spec in place at L3). Not linked yet (the
  server link takes them at L3 with concrete `P`/`Mr`/`Sio`). dd04ec68ce `purgeFile` with its body (axiom gone): spec
  over `srvGoAttachOk` + `MaxWALFiles ↦□ 0` + `threadTokFrom 1`; `srvMonitorCfg`/`srvMonitorsOff` gain the field;
  `Start` via `wp_GoAttach_tokT`; 5 example sites; server Link regenerated. 6569184aad lean (5fb716b5eb) merged.
- **R6 (checked before relying on `storageOver`):** `monitorStorageVersion`'s axiom gives no storage resource; Go
  reaches `MinimalEtcdVersion` (which reassigns `st.w` under `mux.Lock`) only when `UnsafeMigrate`'s target (the cluster
  version) is below the detected storage version (schema.go:69-71); the storage version is 3.5 (detected) or a value the
  monitor wrote (= the cluster version); the cluster version is the members' minimum server version or 3.0 (skipped,
  monitor.go:110) and goes down only through a downgrade (`DowngradeInfoSet`: `apply.rqOk` false, `monitorDowngrade` off
  at `DowngradeCheckTime = 0`). So the branch is dead in every covered run: the invariant fixing `p.w` does not make
  the axiom false (its docstring says "reads" of the WAL; a reopen, `notes/axiom-review/monitor-storage-version-receipt.md`).
- **Next:** L3 (with L4), after the trust-base review: `rnNewStorageOk`/`isWalStorage` restated over `NewStorage`'s post;
  `storage.Release.spec` replaced in place by `ReleaseNext`'s statement and the axiom removed; F2's discharge
  (raft's snapshot conf state canonical, else a model wrap); link the storage proofs in the server's Link.
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial` (`ln -s
  /shared/perennial-c6b39d4f8`, then `rm`); gen-init needs `PERENNIAL_DIR=/shared/perennial-c6b39d4f8`. goose:
  `PATH=/usr/local/go/bin:$PATH etc/goose.py --project etcd --src etcd=/shared/tmp/wallink/etcd --perennial
  /shared/perennial-c6b39d4f8`. `wp_apply` of RLock already runs `wp_auto` (a following `wp_auto` fails: `(try wp_auto)`).
  A WAL spec's `match` pre: `dsimp only` in the side goal. `questions.md` is git-ignored (local only).
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.



### START HERE (2026-11-17, L2 proper: goose config done; STOP on two findings)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`.
  Coordinator: etcd-grove-03. Scope §2-§3, §7-§8; `questions.md` (T1, ReleaseSnapDBs accepted).
- **Done:** 771d63dd6b `storage.toml` translates `NewStorage`, `storage.{SaveSnap,Release,Save,Close,Sync}` with bodies
  (imports `wal`, `walpb`); goose regenerated (`--src etcd=/shared/tmp/wallink/etcd --perennial /shared/perennial-c6b39d4f8`,
  PATH with go); `gen-init` (storage's init runs wal's/walpb's: storage and apply `Init` gain the `Fs`/`log.NewModel`
  instance variables, 24 PkgTables renumbered); `apply/Base.lean` imports wal's `PkgInit`. Built: storage/apply `Init`
  only (no full build yet). The `storage` struct is now translated (its two `sorry -- axiomatized type` gone).
- **Stopped (reported to etcd-grove-03), no spec written yet:**
  (F1) `storage.Release`'s axiom cannot go in L2 alone: a proof needs the storage's representation (RWMutex over
  `p.w ↦ w`, `p.s ↦□ ss`) and layer 1's `ReleaseLockTo` premises (`walOpenWS` share, `walAreaOk`, `walSyncedLb`, AU
  over `walDiskAt`, a synced snap record); its clients (`applySnapshot`, `EtcdServer.snapshot`, `SnapApplyWalk`) get
  only `storageSnap p ss` (opaque) and `walBaseLb (walOf …)` from `rnNewStorageOk`/`isWalStorage` (trusted until L3).
  (F2) `storage.SaveSnap` shares raft's conf-state object in the `walpb.Snapshot` it builds; `walSrvMr.encSnap` is
  `snapEnc (walSnapCanon md)` (conf state nil iff zero, `AutoLeave` present); `csOptA … false` allows a nil
  `AutoLeave` cell and a non-nil zero conf state, so the record's bytes need not be `Mr.encSnap md` (R5's bridge
  assumed canonical). Raft's own `ConfState()` sets `AutoLeave` (tracker.go:148-155); received snapshots: per sender.
- **Planned forms (not yet written):** `storage.storageOver p w ss` (persistent: `p.s ↦□ ss`, `isRWMutexGuard`
  and a thread pool of reader tokens over `P q := p.w ↦{q} w`); methods take/return `threadTok`, otherwise the WAL
  spec's pre/post; `NewStorage` takes `threadBound GF ≤ 2^30` (bounds baseline +1 spec-thread for the storage pkg).
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial`; gen-init needs
  `PERENNIAL_DIR=/shared/perennial-c6b39d4f8`. `questions.md` is git-ignored (local only).
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.


### START HERE (2026-11-17, L2: T1 and the ReleaseSnapDBs axiom done)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`.
  Coordinator: etcd-grove-03. Scope §7-§8, `questions.md` for the decisions. L1 (L1a, L1b) accepted by etcd-grove-03.
- **ReleaseSnapDBs:** round 1 REFUTED, round 2 SURVIVES (`notes/axiom-review/releasesnapdbs.md`; Go tests
  `examples/axiomcx/releasesnapdbs/`). **T1 done** (decided by etcd-grove-03): `storage/SnapHeld.lean` (`snapHeld`,
  sealed, gated in `etc/import-all.txt`), `snapDirInv` sealed with `snapDir_take` (generic, sealed token) and
  `snapDirInv_ss_congr` in `rafthttp/Net.lean`, `SnapRO.snapRmM_take`, `OpenSnapshotBackend.spec` over `snapHeld … R'`,
  `applySnapshot` takes `snapHeld … (monoNatAuthOwn γt 1 nt)`, `ApplyAllSnap`'s two takes. The axiom file
  `api/snap/Snapshotter__ReleaseSnapDBs.lean` added (no client until `storage.Release`'s proof).
- **Next, in order:** L2 proper: `storage.toml` (Scope §2), specs/proofs of `NewStorage`/`Save`/`SaveSnap`/`Sync`/
  `Close`/`Release` (Release from `ReleaseLockTo` + `ReleaseSnapDBs`; then `storage.storage.Release.wp_proof` axiom
  gone), `purgeFile` under `MaxWALFiles = 0`. Then L3 (with L4). `etc/tcb-report.py --check --update` once the new
  axiom is reached and the old one gone (hard stop: trust-base delta).
- **L3 obligations from L1b:** the server's `hardStateAt` becomes `hsOptC` (the Save law's premise; decided at the
  L3 statement stop); `walEntInW` needs `ufWire` and `0 < entrySize c`; `metaEnc` of `etcdserverpb.Metadata` in L3.
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial` (gates.sh does it:
  `ln -s /shared/perennial-c6b39d4f8`, then remove). Lock + later credit and SaveSnapshot pitfalls: History.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.
  **Go:** `cd examples && GOWORK=off TMPDIR=/shared/tmp go test -count=1 -v ./axiomcx/releasesnapdbs/`.

### START HERE (2026-11-17, after L1b)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, lean `3cd4b72599` merged (5ab12b6538); `.lake/package-overrides.json`
  = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03. Scope §7-§8, `questions.md` for the decisions.
- **Done:** Scope (72997e9e36); L0 `St/WalLinkPure.lean`; L1a (shared handle, the five collapses; see History);
  **L1b** (decided by etcd-grove-03: entries by a model wrap, hard state by raft's canonical `Ready`):
  - raft: `hsROC`/`hsOptC` (`InvPb.lean`, `InvPbLog.lean`); `raft.hardState.spec` post `hsROC`; `readyWithoutAccept`,
    `RawNode.Ready` posts and `readyRest` carry `hsOptC` (internal `ownRawNodeReady`, `readyData`, `freshOk`,
    `staleOk` too); clients convert by `hsOptC_hsOpt`; RaftTla regenerated (+ its hand-written `makeTracingState`);
    ledger entry 2026-11-17.
  - `PW/RaftModel/Srv.lean`: `walEntW`/`walEntUnwrap`, `walEncEntW`/`walDecEntW` (injective: the bytes fix the model,
    `entryEncC_ok`), `walSrvMr`/`walSrvU`, `walEntInW`, `walSrvP` (hard states = `walHsIn`; `walHsIn_of_hsOptC`),
    `walSrvPb_laws` (all `WalPbLaws`; `MarshalHsLaw`/`CloneHsLaw`/`WalHsOwn` stay hypotheses as for WalTester).
  - `St/WalLinkPure.lean`: `walFoldChkFrom_map`, `walRead_map` (the fold commutes with `walOpMapE f`, `f` keeping
    indices: `walEntUnwrap_index`).
- **Next, in order:** L2: Go config (`storage.toml`), specs/proofs of `NewStorage`/`Save`/`SaveSnap`/`Sync`/`Close`/
  `Release`, `purgeFile` under `MaxWALFiles = 0`; HARD STOP at the `ReleaseSnapDBs` axiom text (proposal in the
  report of 2026-11-17). Then L3 (with L4).
- **L3 obligations from L1b:** the server's `hardStateAt` becomes `hsOptC` (the Save law's premise; raft's `Ready`
  gives it); `walEntInW` needs `ufWire` (from `entRoC`'s `pbMsg_ufWire`) and `0 < entrySize c` (index ≥ 1 sets
  `Index`); `metaEnc` of `etcdserverpb.Metadata` moved from L1b to L3 (needed only by `walMetaIs`).
- **Pitfalls:** gen-link/gen-init compare only with Perennial linked at `.lake/packages/perennial` (gates.sh does it:
  `ln -s /shared/perennial-c6b39d4f8`, then remove). Lock + later credit and SaveSnapshot pitfalls: History.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
  **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.

### START HERE (2026-11-17, after L1a)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; `.lake/build` from a full c6b
  build at 9702d5707e; `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Decisions** (Scope §7, `questions.md`): plan approved by the user; Q1 L3 lands with L4; Q2 P2 (`--wal-dir` under
  per-member `fsExt` roots, examples' Go absolute); Q3 `NoIoErr` all inodes; Q4-Q6 as recommended (etcd-grove-03).
- **Done:** Scope + Go evidence (72997e9e36); **L0** `St/WalLinkPure.lean` (proved, no trust change): the read bridge
  `walRead_of_fold`, the eager steps `walFoldChkFrom_save_cons`/`_snoc_save`/`_snoc_snap` (`WalSaveOkC` = `WalSaveOk`
  unfolded, so the sealed `WalRecs` can import it), `walCommitLe_of_fold`, `walCommitLeFrom_snoc/_nil`, `walIdxLe_*`.
- **L1a done** (no-twin collapses, Scope §8; shapes accepted by etcd-grove-03): `PW/HandleShared.lean` (the shared
  handle `walOpenWS`, its laws, `ioNone`, `noErr_ioNone`); one spec + one proof each for `Sync` (7eba580698), `Save`,
  `Close` (over `WalCloseSt`), `ReleaseLockTo` (`spec`, corollary `spec_R`); `PW/CalleeCov.lean` chooses the
  callees' two specs by `walCov`; `etc/link_walfs.py` handles `(Sio := ioNone)` binders.
- **SaveSnapshot's room (A) done** (dcb795d4b3, then the SaveSnapshot commit after it): `HandleRoom.lean`
  `walSnapBudget`/`walSaveRoom`/`snapRoom`; `HandleShared.lean` `WalShN.γu`, `walUsed`, γ-indexed `walHdl`
  (`walHdlF` before sharing, `walOpenWS_alloc` also returns `walUsed γ 0`), `walShPers` holds the WAL's
  `isPkgInit` (`walShPers_pkgInit`), AU transformers `walAu_save`/`walAu_snap` (method) and
  `walAu_saveC`/`walAu_snapC` (client); `Save`'s AU carries `walUsed` (`walUsedAfterSave`), room premise
  `walSaveRoom`. **SaveSnapshot: one spec** over `WalSnapSt` (`shared γ q` | `pre …`, `HandleShared.lean`), one
  proof by cases (`wp_shared`, `wp_pre`); `WAL__SaveSnapshotNoErr` gone, `specPre` gone (its proof is `wp_pre`);
  `CalleeCov.walCov_encodeTail`; Create at `.pre` (`Sio := ioNone`, `walPbNone`); WalTester's `member__saveSnap`
  shares the handle. Links regenerated; both Links and the importers' leaves build.
- **Decided (etcd-grove-03, 2026-11-17):** the server SaveSnap law old → new APPROVED (with Save's matching
  `walUsed` update); the collapse's forms ACCEPTED; wire vs model: (i) if provable, else (iii); (ii) out.
- **Next, in order:** L1b by **(iii)** (the check below rules out (i) for entries), stop if a closed statement
  would change; merge lean (≥ 3cd4b72599, then `.lake/package-overrides.json` stays the c6b manifest); end-of-L1
  full build via the build slot (retry on 143); `etc/tcb-report.py --check` and `--collection` for
  `wal-fsext.txt` and `wal-tester.txt`; report the L1 boundary; then L2 (HARD STOP before `ReleaseSnapDBs`).
- **Pitfall (lock + later credit):** a method needing the handle before its first resolution after `Lock` takes
  `Lock` with `+noauto`, steps the deferred `Unlock`'s resolution by hand (`wp_go_step_receipt'`, its `£ 1`), then
  `wp_raise_receipt` at the next resolution (`WAL__Save.lean`, `WAL__SaveSnapshot.lean`). A spec whose pre/post is a
  `match` on a state: `dsimp only` in the call's side goal. Build the Links before committing (lean-check once hid
  an unknown identifier).
- **Pitfall (SaveSnapshot):** the receipt is raised at `encode`'s resolution: `simp only [SnapshotType]` first,
  or `wp_to_resolve` stops at the record's literal. A multi-line `{ h with … }` in a tactic term: fields of a
  continuation line must align with the first field's column.
- **Open (for L3/L5):** nothing produces `walOpenWFR` yet (Create's/ReadAll's posts give `walOpenWF`; room is an
  open layer-1 decision, `notes/wal-units/noioerr.md`): the server's shared handle needs the fresh room from
  bootstrap's slot (L3, trusted) and, in L5, from `Create` (headers < 2^43) and the restart's `ReadAll` (a tail bound).
- **Pitfalls:** WAL Go sources at the pin: `/shared/tmp/wallink/etcd` (shallow fetch of `8c28a4296`); `.lake/go-src/etcd`
  is older. `E/WalApi.lean`'s header "NOT YET IN USE" is stale (fix in L3). `WalViews.lean` is over the old `absDiskExt`.
- **Check:** `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`
  (`--stop` before builds and at the end). **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`.

### L1b by (iii): cost stop (2026-11-17; reported to etcd-grove-03; no Lean changed)

- **Why (iii) is not internal to RaftModel/WalApi.** Layer 1 fixes `Mr : WalMarshal` (model -> bytes) as a
  parameter of `walInv` (`PW/Inv.lean:2128`), allocated before any entry exists, and every stream function
  (`opDs`, `cutHdrDs`, `segsDs`, `recsOfSegs`, `tailStream`, `tailRecs`, `allRecs`, `segStream`,
  `St/WalEncRecs.lean`, `St/WalEncSegs.lean`, `PW/Handle.lean`) computes the bytes from `H.map WalOpG.toM`.
  Per-record bytes need a new argument (an annotated history `X` with `strip X = H.map toM`, kept per directory
  in `walInv` and in the tail record, maintained by Save/SaveSnapshot/cut/Create/ReadAll/crash): 105 files,
  919 uses of the stream functions, 176 of `map WalOpG.toM` (57 files): est. 2-4k lines changed, about (ii)'s cost.
- **Entries alone are cheap (no layer-1 change):** the server's WAL-level model of content `c` keeps term/index/
  type and puts `entryEncC c` in `Data'` (`Mr.encEntry` := those bytes when the model is such a wrap of a `ufWire`
  content, else injective stand-in bytes as `walEntJunk`); round trip from `entryEncC`'s injectivity on `ufWire`
  (MsgAppV2.lean:567-570). The history then holds wrapped models; L0/L3 map them back (fold commutes with maps
  keeping Index/Term, ~100 lines). Est. 300-600 lines.
- **The hard state is the blocker:** `WalOpG.save (h : HardStateM)` (trusted `GooseLang/Ext/AbsDisk/Impl.lean:83`)
  has no room for content, and `cut` repeats the last state record (wal.go:931, `w.state = s`, :1098). Options:
  (a) raft's exported Ready results give the hard state canonical (`raft.hardState` builds all three cells, uf = []:
  `raft__hardState.lean:31-35`): a stronger post on `RawNode.wp_Ready`/`node.wp_Ready`/`isReadyChan_recvAu`
  (exported statements: user/coordinator stop); (b) layer 1 over per-record state bytes (the annotated history
  above, state part only; most of the 2-4k); (c) `walInv`'s `encState` a ghost map extended at first use, with a
  no-conflicting-repeat premise on Save (raft's hard-state monotonicity at `raftNode.start`: not exported today).
- Recommendation in the report: entries by the wrap; hard state by (a).

### L1b at the R5 stop (2026-11-17; HARD STOP (b), reported to etcd-grove-03; no Lean changed for L1b)

- **R5 (fraction vs frozen): no client change.** `storage.SaveSnap` (S/storage/storage.go:59-70) shares raft's
  `Index`/`Term` cells and `ConfState` object in its `walpb.Snapshot`; layer 1's `walSnapAt` needs them frozen.
  The law's `smPtsV mp dq' md` has the cells `cellRO` already; only the conf state is at `dq'`. Both callers pass
  a discarded metadata (`EtcdServer__snapshot.lean:366`, `raftNode__start.lean:616` via `srv_ownSnapS_meta`'s
  persistent facts): the law fixes `dq' := DFrac.discard`. Bridge (L1b lemma): `csPts … DFrac.discard` gives
  `csRoC` with `uf = []` (`PbContent.lean:704`) → `walCsRoC` at `walCsCanon`.
- **New finding (content vs model):** layer 1's `WalMarshal` encodes models; `walRaftP` (PW/RaftModel) needs the
  canonical wire content (`walEntIn`: `entRoC l (walEntCanon e)`; `walHsIn`: `walHsCanon h` unless empty). The
  server's entries are any content of the model (`walSaveEnts true`: `∃ c, entRoC l c`, `c.uf` and field presence
  free; MsgApp entries are unmarshalled) and `hardStateAt = hsRO` leaves `pbMsg … uf` free; protobuf-go writes
  presence and unknown fields, so the records' bytes are not a function of the model. Options: (i) a fact that the
  server's entries/hard states are canonical (needs `uf = []` and raft's presence pattern; likely false for
  received entries); (ii) layer 1 over contents (`WalOpG` over `EntryC`/`WalHsC`, `Mr` over contents, `ReadAll`
  returns contents): several k lines; (iii) `Mr` over contents with the per-record bytes in a ghost map read by the
  crash invariant. Recommendation in the report.
- **(i) vs (iii), checked 2026-11-17 (read-only):** entries cannot be shown canonical: `appendEntry`
  (raft.go:812-819) clones the proposer's entry and sets only Term/Index; proposals build `&pb.Entry{Data: data}`
  (node.go:472, rawnode.go:94; no `Type`, while `walEntCanon` needs `Type = some`); received MsgApp entries keep any
  `uf` within `ufWire` (`MsgAppV2.lean:87,108`, `msgAppV2Decoder__decode.lean:190`) and reach `Save` uncloned.
  Hard state: Go's `r.hardState()` sets all three cells with `uf = []` (raft.go:504-510; proof
  `raft__hardState.lean:31-35`), but `raft.hardState.spec` returns only `hsRO` (uf, nil cells free); making it
  canonical would restate raft library results (`Proof/go_etcd_io/raft/v3/Results.lean`: `RawNode.wp_Ready`,
  `node.wp_Ready`, `isReadyChan_recvAu`). So **(iii)** for both: `Mr` over contents (entry bytes `entryEncC c`, any
  `uf` with `ufWire`; the decoder's round trip from `entryEncC`'s injectivity on `ufWire` contents, as
  `MsgAppV2.lean:567-570` uses), each record's bytes in a ghost map the crash invariant reads, the history over
  models. Expected internal to the WAL model (`RaftModel/EntCodec.lean`, `Pb.lean`, `Marshal.lean`) and
  `WalApi.lean`; WalTester's canonical instance stays a special case.
- Server `SaveSnap` law, old → new: in the report (and `/shared/tmp/wallink/l1b-r5.md`).

### Older

### START HERE (2026-11-17, Scope)

- **Branch** `wal-link` in `/shared/etcd-grove-wallink`, off `lean` `9702d5707e`; no `.lake/build` (disk);
  `.lake/package-overrides.json` = `/shared/tmp/manifest-c6b.json`. Coordinator: etcd-grove-03.
- **Done:** the Scope, `notes/wal-link-scope.md` (HARD STOP: Scope ready for review); Go evidence
  `examples/wallink/link_test.go` (C1-C7), all pass at the etcd pin `8c28a4296`
  (`cd examples && GOWORK=off TMPDIR=/shared/tmp systemd-run --scope -q -p MemoryMax=32G go test -race -count=1 -v ./wallink/`,
  ~95 s, most of it C1's fsyncs; last run log `/shared/tmp/wallink/test-run.txt`). No Lean changed.
- **Next, in order, once the Scope is approved:** L0 (pure read bridge, `St/WalHistLemmas.lean` neighbours) ∥ L1a
  (layer 1's shared handle, `PW/Handle.lean`) ∥ L1b (the server's `WalPbIn`/`WalMarshal`; check R5 first: are
  `hardStateAt` and raft's snapshot conf state frozen?); then L2 (`storage.toml`, `serverstorage` proofs,
  `ReleaseSnapDBs` axiom: HARD STOP), then L3 with L4 (Q1). Scope §5.
- **Open decisions (Scope §5):** Q1 land L3 with L4 (recommended); Q2 placement P2, `DedicatedWALDir` under
  per-member `fsExt` roots (recommended; changes the examples' Go); Q3 `NoIoErr` on all inodes now; Q4 the
  received snapshot's bounds from the cluster's room invariant; Q5 take `walFiles`' exclusivity and the `walSnapRec`
  witness; Q6 drop the `sized = false` law.
- **Pitfalls:** the WAL's Go sources at the pin are not in any local checkout (`.lake/go-src/etcd` is at
  `6e8f0c004c`); a shallow fetch is in `/shared/tmp/wallink/etcd` (`git fetch --depth 1 https://github.com/upamanyus/etcd 8c28a4296f…`),
  and the module cache has `server/v3@v3.0.0-20261115085855-8c28a4296f16`. `E/WalApi.lean`'s header still says
  "NOT YET IN USE" (stale since R2b-1; fix it in L3, not in a Scope commit). `WalViews.lean` is over the old
  `absDiskExt`, not `WalFs`: L0 states its lemmas over `WalHist` only.
- **Build (L1+):** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build TARGET`; a `.lake/build`
  must be seeded or moved here first (the coordinator; `df -h /shared` ≥ 40 GB before any `cp -a`).
