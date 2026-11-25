# P5 (etcd_safe #50/#51, D6-T2): the server's crash-aware durability invariant — handoff

## START HERE

- **Date**: 2026-11-25 (session 1). **Branch** `etcd-safe-p5`, worktree `/shared/etcd-grove-p5`.
- **Base**: `etcd-safe-main-r3/2026-11-25` @ `57e4d118b7`, then its P7 update `5a1c41d945` merged in
  (`fd7630f9da`) (posted green on #50 07:18Z; same Perennial pin
  `fce59af75`), with `etcd-safe-d6t2/2026-11-24` @ `efd5966fe4` merged (`97ef57a342`: P8's
  `InvWalCrash`/`InvWalCrashLaws`/`WalRecsH` kept, d6t2's notes section as §10T2). (The first base,
  `etcd-safe-p8-stack`, was cancelled; the work done on it was cherry-picked.)
- **Build**: `export TMPDIR=/shared/tmp`; `--packages=/shared/tmp/manifest-fce59af7.json` (check r3's
  Perennial pin first); edit loop `etc/lean-check.py`; targeted `/shared/tmp/build-slot.sh lake ... build`.
- **State** (2026-11-25): the decision is approved (coordinator-E, #50 07:04Z). Done: the pure steps
  (`InvWalCrashPure`), the six step laws (`InvWalCrashSteps`), the contract's `Save`/`SaveSnap` over `walRecsH`
  (`isWalStorage`, `RnNewStorage`), the boot slots with history (`walOpenedH`, `wal.bootOk`, `wal.restartOk`,
  `wal.Create.specSrv`; ledger entry). Built: the 49 importer leaves of the change
  (`etc/importers.py --leaves`) on `4167bcf956`, fk-lean2, 13,792 jobs, exit 0, and again after merging `5a1c41d945` (13,794 jobs, exit 0); `etc/tier-check.py --check` ok.
  The eager commit bound: `wal.restartOk` states `walCommitLeFrom walFresh Hs` (the eager fold's), which implies
  the approved reader form `walCommitLe` (`walCommitLe_of_fold`) and is what `histOk_save` needs (ledger entry).
  Left: the integration (below); a first WIP of its `InvRaftNode` part (`RNNames.walK`, `raftState` out of
  `rnDrv`/`rnBusyN`/`rnPendEnter`/`rnBusyS`, `rn_enter{,S}` removed, `isRaftNode`'s `#Harm`) is in
  `git stash` "P5 integration WIP". Remote builds: fk-lean2's `wt/etcd-safe-p8`
  through the scratch ref `etcd-safe-p8` (a copy of `fklean1-check.sh` resolving `LOCAL_REV=etcd-safe-p5`).

## What exists (P8's proposal (3) + d6t2's WIP)

- `storage/WalRecsH.lean`: `walRecsH h σ Hs sized` (records with their history), `walRecs_iff_H`,
  `walRecsH_fold`, `walRecsH_crash` (P8).
- `etcdserver/InvWalCrash.lean`: `WalViewK`, `crashOk`, `CrashReadsHold`, `HistReadOk`, `WalNamesK`,
  `rnPendRec`/`rnPendK`, `rnDurBodyK`, `rnDurInvK`, `rnTakenK`, `rnWalViewK`; statements
  `walSaveH.law`, `walSaveSnapH.law`, `rnDurK_{alloc,save,saveSnap,enter,ownSnap,take,crash}.law`.
- `etcdserver/InvWalCrashLaws.lean`: `rnDurK_crash_law_holds` proved.

## Plan

1. **Pure step lemmas** (new `etcdserver/InvWalCrashPure.lean`): for `CrashReadsHold`/`HistReadOk` across
   `Hs ++ [save]` (new prefix: `walRead_of_fold` + `walCommitLe_of_fold`; needs the eager
   `walCommitLeFrom walFresh Hs` kept in the body as an extra conjunct), `Hs ++ [snap]` (received: the
   new prefix reads as the old, `walReadsBack_snap`-style; own: `walOwnSnap_holds` per prefix), and the
   commit-only *enter* (`ImgOk` monotone under `RaftState.next` keeping `wcommit`).
2. **The laws' proofs** (`InvWalCrashLaws.lean`): alloc, save, saveSnap, enter, ownSnap, take, plus K
   versions of `rnDur_viewOk`/`rnDur_read_au`.
3. **The contract with the history**: `isWalStorage`'s `Save`/`SaveSnap` over `walRecsH` with the history
   and the synced bound (`RnNewStorage.lean`'s `walSave_law`/`walSaveSnap_law`: `storage.Save.spec`'s post
   already has `walSyncedLb dir (|d.H|+1)` under `walMustSync`), the old laws derived (`walRecs_iff_H`).
4. **Integration**: `RNNames.wal` becomes `WalNamesK` (`abbrev RNNames.wal := γ.walK.ν` keeps `γ.wal.app`
   etc.); `raftState` leaves `rnDrv`/`rnBusyN`/`rnPendEnter`/`rnBusyS` for the invariant; the loop's two
   `Save` sites (`raftNode__start.lean` ~l.690, ~l.1515) use `rnDurK_save`, the two *enter* sites (~l.721,
   ~l.1540, already under `wp_ncfupd`'s `notCrashed`) `rnDurK_enter` (two credits needed there);
   `rnDurK_saveSnap` at the received snapshot; `EtcdServer__snapshot`/`SnapApplyWalk` the K `ownSnap`/read;
   `onStop` `rnDurK_take`; `bootstrappedRaft.newRaftNode` keeps the crash token (`nodeVacant_arm`, not
   `_armD`) and allocates `rnDurInvK` after `StartNode`/`RestartNode` (raftState is only then available);
   `wal.bootOk_start`/`wal.restartOk_start` hand over the records instead of allocating `rnDurInv`.
   Files: `InvWal`, `InvWalCrash*`, `WalApi`, `RnNewStorage`, `InvRaftNode`, `InvRaftLoop`, `NodeStart`,
   `InvNodeStart`, `bootstrappedRaft__newRaftNode`, `raftNode__start`, `raftNode__onStop`, `raftNode__stop`,
   `EtcdServer__run`, `EtcdServer__snapshot`, `SnapApplyWalk`, `NewServer`, `NewServerR`, `StopShutdown`,
   `NodeBridge` and the Spec files naming `rnDurInv` (`raftNode__stop`, `EtcdServer__{run,applyAll,
   applySnapshot,snapshot,snapshotIfNeededAndCompactRaftLog}`, `raftNode__onStop`).

## Decision (needed before the allocation can be discharged)

`rnDurK_alloc.law` needs, of the WAL's history `Hs` at allocation, a synced mark `n` and every prefix from
`n` reading records that hold the start state (`CrashReadsHold`), with `HistReadOk Hs n`. The boot slots
give only `walRecs h σ true` (the history hidden; an arbitrary history whose eager fold is `σ` can break
both). What is derivable: `walSyncedLb h.dir 0` (from `walRecs`' `walNamed`). What is needed:

- **first start**: the history is empty (`walDurFresh` has `H := []`: true of Go); i.e. `wal.bootOk`'s body
  (and `wal.Create.specSrv`'s post, an unproved hypothesis whose proof builds exactly `walDurFresh`) gives
  `walRecsH h walFresh [] true` instead of `walRecs h walFresh true`;
- **restart**: `wal.restartOk`'s body gives the history synced and reading (`walSyncedLb h.dir |Hs|`,
  `walIdxLe (2^61-1) Hs`, `walCommitLe Hs`; write-mode `ReadAll` syncs; the rest is what T2's own invariant
  carried across the crash, or the graceful stop's `walFiles` must carry).

`wal.bootOk` is inside `bootstrapContract`, a named premise (`Hprem`) of the dist top-level statements; so
this is a change to a top-level premise's meaning (stronger), reported before doing it (rule #8).
