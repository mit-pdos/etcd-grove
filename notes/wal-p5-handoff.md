# P5 (etcd_safe #50/#51, D6-T2): the server's crash-aware durability invariant — handoff

## START HERE

- **Date**: 2026-11-25 (session 1; session 4 the newest State). **Branch** `etcd-safe-p5`, worktree `/shared/etcd-grove-p5`.
- **Base**: `etcd-safe-main-r3/2026-11-25` @ `57e4d118b7`, then its P7 update `5a1c41d945` merged in
  (`fd7630f9da`) (posted green on #50 07:18Z; same Perennial pin
  `fce59af75`), with `etcd-safe-d6t2/2026-11-24` @ `efd5966fe4` merged (`97ef57a342`: P8's
  `InvWalCrash`/`InvWalCrashLaws`/`WalRecsH` kept, d6t2's notes section as §10T2). (The first base,
  `etcd-safe-p8-stack`, was cancelled; the work done on it was cherry-picked.)
- **Build**: `export TMPDIR=/shared/tmp`; `--packages=/shared/tmp/manifest-fce59af7.json` (check r3's
  Perennial pin first); edit loop `etc/lean-check.py`; targeted `/shared/tmp/build-slot.sh lake ... build`.
- **State** (2026-11-25, session 5): **stopped (priorities: M1 first, #50 16:48Z); raft law not
  provable additively; no Lean changed.** Merged
  `etcd-safe-main-r4/2026-11-25` @ `1c2958cbb4` (`b11c0ca87c`, clean; `etc/api/raft.txt` keeps r4's
  `LeaderCompleteLaw`; same Perennial pin `fce59af75`). The lead approved (#50 16:11Z) the raft law
  additively; it is **not provable additively**: neither `readyRest`, nor `nodeDriver` after the receive,
  nor the old `raftState` ties the batch's durable log to the committed log above the old commit (the
  fact lives in `run`'s in-memory state until *enter*). Ledger entry's Decision has the evidence and an
  alternative needing no raft change: `v'.l := L` at *enter* (`raftState_logView` on the entered
  state), the pending record's `ViewOk` discharged at *enter* or, at a crash, after `readyEnterCrash`.
  **Build of the merge** (fk-lean2, `fklean1-check.sh … etcd-safe-p5` over the 157 leaves of
  `etc/importers.py --leaves --git 0c9856a863`, list at `/shared/tmp/p5-leaves.txt`): the client's ssh
  dropped (EXIT 255) at job 8697/9426 with **no error** up to there; not finished. Rerun the same command
  (incremental on fk-lean2's `wt/etcd-safe-p5`) before relying on the merge.
  **Next** (when crash work resumes): finish that build; the lead's choice (a raft change to
  `readyRest`/`nodeDriver`, or the server-side alternative); then (b) 1, 2, 4, 5 and the view change;
  then P5-RESTART (with (a) from T10's `bootstrapCrashContract.law`).
- **State** (2026-11-25, session 4): **stopped before (b)'s Lean; ledger entry pending.** Merged
  `etcd-safe-p6b` @ `9615f76264` (`bd51f55338`: `wal.Discard.spec`, `walDiskAt_crash_blank_keep`; clean).
  While scoping (b) step 3: the K form of `ViewOk`/`ImgOk` from a snapshot certificate is not provable. A
  record `snap m` dropped at a restart is kept again once a `Save` commits past `m`; if that `Ready`'s
  committed entries stop below `m` (raft's `maxApplyingEntsSize`), the crash prefixes read records based at
  `m`, and `StorageHolds v'.S` of them needs raft's durable term at `m` = `m.Term'`, which nothing exported
  gives (`ReadyRestFacts` ties the batch's log to the committed log only on `ce`). Ledger: "raft's
  `readyRest` (the batch's facts) -- the batch's durable log is tied to the committed log only through the
  handed entries" (2026-11-25), proposing a raft law giving the committed log `L` up to the batch's commit,
  held by the batch's durable log; with it the view hands `v'.l := L` and `ViewOk`/`ImgOk` need no K form.
  Steps 1, 2, 4 are not done alone: the contract's AU (step 1) is what `rnDurK_save.law` hands the loop's
  `Save`, so changing it moves the body (step 2), whose `Save` step needs step 3. **Next**: the lead's (and
  raft's owner's) decision on that entry; then (b) 1-5 as planned, step 3 replaced by the loop's `v'.l := L`.
- **State** (2026-11-25, session 3, after #50 15:33Z: (b) then (a) approved, (a) through the restart slot):
  **(a) stopped, (b) begun.** (a) cannot go through `wal.restartOk` alone: the slot is the post of the
  interim axiom `bootstrapCrashContract.law` (C-I2) / `bootstrapRestartContract`, from `srvFilesC`, whose
  `walFilesC` hides the history; T7's producer makes the image, not the slot. Fields needed: ledger entry
  "`wal.restartOk` over the reader's fold", Decision. Waiting for the lead. P5-RESTART stays (`sorry` in
  `rnRestartAllocK_law_holds`; not in `etc/tcb-baseline.txt`, whose `sorry` lines it lists none of: whether a root reaches it needs `etc/tcb-report.py --check` on a full build, not run). **(b) done so far**: `walHistH h Hs
  sized` (`storage/WalRecsH.lean`, additive: `walRecsH` without the fold row; `walRecsH_iff_hist`,
  `walRecs_iff_hist`, `walHistH_{synced0,crash,saveAU,saveSnapAU}`). **(b) next, in order**: (1) the
  contract (`isWalStorage`, `RnNewStorage.lean`'s `walSave_law`/`walSaveSnap_law`, `walSaveH.law`/
  `walSaveSnapH.law`) over `walHistH` with the AU's pure premise `∃ σ, walRead Hs = some σ ∧ WalSaveOk σ es`
  (or none: layer 1 needs none, `walHistH_saveAU`); (2) `rnDurBodyK`: `walHistH h Hs true` with
  `walRead Hs = some σ` (σ the reader's records; `recsOf vk.1 σ` only for the pending received snapshot),
  `HistOkK` without `walCommitLeFrom walFresh Hs`; (3) a K form of `ViewOk`/`ImgOk` whose base may exceed
  the handed log when a certified snapshot record (`walHistCerts`, in the body) gives a committed log of
  length `m` (`snapshotValid` → `isCommittedLogLb` at `m`; find the lemma `walSnapCert` users take); (4) the
  step laws' proofs (`InvWalCrashPure`, `InvWalCrashSteps`, `InvWalCrashLaws`) and `wal.restartOk`'s body
  (`walHistH`, `walRead Hs = some σ`; `wal.restartOk_startK`, `rnRestartWal`); `raftNode__start`'s call
  sites if the laws' AU shapes change; (5) delete `walRecsH` once unused. Then (a) as the lead decides;
  then merge `etcd-safe-p6b` @ `9615f76264` (P6b done: `wal.Discard.spec`, `walDiskAt_crash_blank_keep`;
  `storage/wal/` caution lifted) and use them in bootstrap's contract.
- **State** (2026-11-25, session 2, after #50 15:22Z item 1): **stopped, no Lean changed.** The approved
  restatement (`wal.restartOk` and the post-restart contract over `walRead Hs`) does not discharge P5-RESTART:
  (1) the `sorry` is `walHistCerts` of the restart's history, and a snapshot record dropped at the restart
  (above its commit) is read again once a later `Save` commits past it, so its certificate must cross the
  crash; nothing carries it (`wal.restartOk` names no cluster; the images and `rnDurK_crash.law` hold only the
  read records' certificate). (2) After such a restart the contract's `Save` is no step of the reader's fold
  (`walRead (Hs ++ [save])` re-bases at the dropped snapshot when the commit reaches it; the eager fold refuses
  `WalSaveOk`), so `walRecsH`'s fold row, `walSaveH.law`'s post and the invariant's `ViewOk`/`ImgOk` change
  too. Ledger: "`wal.restartOk` over the reader's fold -- not enough for P5-RESTART" (2026-11-25), with the
  proposed changes (a) certificates through the crash law and the restart slot/image, (b) the contract over the
  history. **Next**: the lead's decision on (a)/(b); then (b) first (it fixes the contract and every step law),
  then (a) with T7's producer. Not done either: `etc/tcb-baseline.txt` for P5-RESTART.
- **State** (2026-11-25, later): **the integration builds, restart allocation isolated.** `rnDurInvK` is in
  `isRaftNode`/`rnWalTokA` (with the T6 placeholder `⌜γ.walK.sd = fun _ => True⌝`), allocated in
  `bootstrappedRaft.newRaftNode` after `StartNode` (`rnDurK_alloc_fresh`) and after `RestartNode` (the named
  hypothesis `hRestartAlloc : rnRestartAllocK.law`, linked by `rnRestartAllocK_law_holds`, which holds the one
  labelled `sorry` **P5-RESTART**: the restart slot carries no `walHistCerts` for its history; pending #50's
  restatement of `wal.restartOk`). The loop: `Save` through `rnDurK_save.law` (a saved `rnPendRec`), *enter*
  through `rnDurK_enter.law` (synced, or commit-only via `imgOk_commitOnly`); the received snapshot's
  `SaveSnap` through `rnDurK_saveSnap.law` and its batch's *enter* moved after the explicit `Sync` (below);
  `onStop` through `rnDurK_take`; `EtcdServer.snapshot`/`SnapApplyWalk` through `rnDurK_ownSnap`/
  `rnDurK_read_au`. P6b (`2d2f3cc470`, the WAL's incarnations) merged (`f426a79f6b`).
  Invariant changes found on the way: `HistOkK` gains `HistCommitMono` (a restart may enter a durable commit
  above the last saved one, so the commit-only *enter* is bounded by the entered hard state's commit);
  `rnDurK_save.law` takes the commit's monotonicity; `rnReadyData`/`rnReadySnap` state `S' = readyDurable …`
  and `S'.commit ≤ S'.last`. **The storage contract's `Sync` now syncs**: `Save`'s post gives the handle's
  length bound `walLenLb … (|Hs|+1)` and `Sync` takes `walLenLb … n` to `walSyncedLb … n` (layer 1's
  `storage.Sync.spec` already does): a snapshot `Ready` whose `Save` need not sync (`raft.MustSync` ignores
  the commit) is durable only after etcd's explicit `Sync` (raft.go: "Force WAL to fsync its hard state"),
  so its *enter* follows it (the commit-only route cannot hold: the new state's snapshot base is above
  every old record's).
  Built (fk-lean2): `NodeStartLinked`, `NewServer`, `NewServerR`, `newRaftNode`, `raftNode__onStop`,
  `raftNode__start`, `EtcdServer__snapshot`, `SnapApplyWalk`, `RnNewStorage`; the leaves of the whole change
  (`etc/importers.py --leaves --git 5a1c41d945`, 58 without the `notes.` target): fk-lean2, 14,036 jobs, exit 0;
  the only `sorry`s in the tree's own files are P5-RESTART and the two that predate P5 (`NewServerCrash`,
  `MemstorageApi`).
  `etc/tier-check.py --check` ok. `etc/tcb-baseline.txt` not yet updated for P5-RESTART (needs a local build).
- **State** (2026-11-25, earlier): the decision is approved (coordinator-E, #50 07:04Z). Done: the pure steps
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
