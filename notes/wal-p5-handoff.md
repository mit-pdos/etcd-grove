# P5 (etcd_safe #50/#51, D6-T2): the server's crash-aware durability invariant — handoff

## START HERE

- **Date**: 2026-11-25 (session 1; session 8, 2026-11-26, the newest State). **Branch** `etcd-safe-p5`, worktree `/shared/etcd-grove-p5`.
- **Base**: `etcd-safe-main-r3/2026-11-25` @ `57e4d118b7`, then its P7 update `5a1c41d945` merged in
  (`fd7630f9da`) (posted green on #50 07:18Z; same Perennial pin
  `fce59af75`), with `etcd-safe-d6t2/2026-11-24` @ `efd5966fe4` merged (`97ef57a342`: P8's
  `InvWalCrash`/`InvWalCrashLaws`/`WalRecsH` kept, d6t2's notes section as §10T2). (The first base,
  `etcd-safe-p8-stack`, was cancelled; the work done on it was cherry-picked.)
- **Build**: `export TMPDIR=/shared/tmp`; `--packages=/shared/tmp/manifest-fce59af7.json` (check r3's
  Perennial pin first); edit loop `etc/lean-check.py`; targeted `/shared/tmp/build-slot.sh lake ... build`.
- **State** (2026-11-26, **P5 session 8**): **(b) step 1 built green; steps 2-5 not started (ledger entry
  written).** Build of `f0f5ec4d43` on fk-lean2 (`fklean1-check.sh … etcd-safe-p5` over
  `/shared/tmp/p5-s8-leaves.txt`: `p5-s6-leaves-nonotes.txt` plus `etc/importers.py --leaves --git a601c25a54`,
  `notes.*` dropped; 157 leaves): **exit 0, 19500 jobs** (log `/shared/tmp/p5-s8-build2.log`). It covers session
  6's `rnDurK_crash.law`/`walHistCerts_take`/`memberDur_crash`, the r4 merge, step 1 and `raftState_logViewE`
  (both trees). The one failure (`/shared/tmp/p5-s8-build1.log`) was `isWalStorage_intro`'s `hSave`/`hSnap`
  hypotheses (`WalApi.lean`), still over `walRecsH` while the contract and `walSave_law` were over `walHistH`:
  restated over `walHistH` (`f0f5ec4d43`). **copy-part**: `etc/copy-part.py --check` passes (RaftNoAx 0 differ,
  KvRaft 0 differ), locally and on fk-lean2, with `PERENNIAL_DIR` set to a checkout at the pin
  (`/shared/perennial-fce59af75`; fk-lean2 `/home/ubuntu/eg/perennial-fce59af75`). The `KeyError:
  'internal.testlog'` comes from no `etc/` script: without `PERENNIAL_DIR`, gen-init reads the shared
  `.lake/packages/perennial`, which is at `ddc0f0acc`, not at the pin `fce59af75` (and fk-lean2's worktree has
  no `.lake/packages`). The hand-made `RaftNoAx/` copy of `DurableLogView` is byte-identical.
  Ledger entry "`rnDurBodyK` and its step laws" (2026-11-26, `35ce623d08`) covers steps 2-5. **Next: steps 2-4
  form one change.** Once the body holds `walHistH h Hs true ∗ ⌜walRead Hs = some σ⌝`, no law whose update is
  over `walRecsH` (`rnDurK_save`/`saveSnap`/`ownSnap`, `rnDurK_alloc`, `rnRestartWal`, `rnDurK_crash`'s callback)
  can be proved, because it must produce the eager fold. So restate them together, with their callers:
  `raftNode__start`'s, `RaftLoopFreeze.lean:633`, `MemberCrash.lean` (`walRecsH_crash`/`walRecsH_gen`, which need
  `walHistH` versions), `NodeStart.lean:790` and `InvNodeStart.lean:358` (`walRecsH h walFresh [] true`).
  The pure crux is a `walRead_snoc_save` (`InvWalCrashPure.lean`, beside `walRead_snoc_snap`). A `Save` that
  raises the commit re-keeps the snapshot records it now covers, so `walRead (Hs ++ [save hs es])` is
  `walSave (recsOf v σ) hs es` only under the pending snapshot's facts: `walSnapStep` `m` at or below the new
  commit, and no other dropped record (by `PendOkK`/`crashOk`). `histOk_save`/`histOk_restart`/`histOk_fresh`
  are restated over the read (drop `walCommitLeFrom`, the `hf` premises).
- **State** (2026-11-26, **P5 session 7**, stopped at the context rule): **(b) step 1 and `raftState_logViewE`
  written, UNBUILT** (`0612182c1f`, under session 6's handoff `16fb93b1de`). Step 1: `isWalStorage`'s
  `Save`/`SaveSnap` updates over `walHistH` (no fold, no premise); direct laws `walSaveHist_spec`/
  `walSaveSnapHist_spec` (`WalApi.lean`); `walSaveSized_spec`/`walSaveSnapH_spec` derived through
  `walRecsH_au_toHist` (`WalRecsH.lean`; `Save`'s refusal arm now hands back the history's update, which its
  only user `walSaveRn_spec` drops); `walSave_law`/`walSaveSnap_law` (`RnNewStorage.lean`) through
  `walHistH_saveAU`/`walHistH_saveSnapAU`; `walSaveH.law`/`walSaveSnapH.law` restated over `walHistH`
  (`walSaveH_law_holds` = `walSaveHist_spec`); ledger entry 2026-11-26 "the WAL contract's `Save`/`SaveSnap`".
  `raftState_logViewE` (`raft/v3/DurableLogView.lean`, mask `Em ⊇ ↑N`; `raftState_logView` its `⊤` case); its
  `RaftNoAx/` copy updated by hand with copy-part's import rewrite (`etc/copy-part.py` crashed here in
  `gen-init.py`, `KeyError: 'internal.testlog'`: rerun it on the build host before relying on `--check`).
  Session 6's queued build never ran (lake refused the `notes.*` targets). **Next**: build `16fb93b1de` with
  `/shared/tmp/p5-s6-leaves-nonotes.txt` plus `etc/importers.py --leaves --git a601c25a54` (no `notes.*`); fix;
  then (b) steps 2-5 as below.
- **State** (2026-11-26, **P5 session 6**): **(a)'s P5 part done (`rnDurK_crash.law` gives the certificates);
  (b) planned under the approved alternative, no (b) Lean yet.** Merged `etcd-safe-main-r4/2026-11-25` @
  `1b9cef43df` (`3dfa5ac91a`; notes and `etc/tcb-collections/etcd-dist.txt` only). The lead approved (b)'s
  server-side alternative (#50 2026-11-25T18:04:00Z, item 6: `v'.l := L` at *enter* from `raftState_logView`,
  the crash law entering the pending batch first; only `rnDurK_save`/`rnDurK_enter.law` change; the raft law
  withdrawn) and (a)'s image route (16:06:56Z: T10 does `walFilesC`/`srvFilesC`/`bootstrapCrashContract`, P5
  gives the certificates). Done: **`rnDurK_crash.law`** (ledger 2026-11-26): `Φ : WalHist → StorContents →
  IProp`, the callback gives `Φ (Hs.take j) σ`, the post's live disjunct `∃ S σ l Hc, Φ Hc σ ∗ … ∗
  ⌜… ∧ walRead Hc = some σ⌝ ∗ … ∗ walHistCerts γn.cl νk.sd Hc` (`walHistCerts_take`, `InvWalCrashLaws.lean`);
  T7's `memberDur_crash` passes `fun _ σ => walFilesC …` and drops `Hc`'s facts (T10 threads them into
  `walFilesC`'s history and the image row). **Unbuilt at handoff** (stopped at the context limit): build of
  `4022e9a46a` queued on fk-lean2 at handoff, command `FKLEAN_HOST=fk-lean2 /shared/tmp/fklean1-check.sh
  /shared/etcd-grove-p5 etcd-safe-p5 $(cat /shared/tmp/p5-s6-leaves-all.txt)` (160 leaves: session 5's
  `/shared/tmp/p5-leaves.txt` plus `etc/importers.py --leaves --git 3dfa5ac91a`), log
  **`/shared/tmp/p5-s6-build2.log`** (ends `EXIT n`). Next session: read it first; if unfinished, rerun the same
  command (incremental in fk-lean2's `~/eg/wt/etcd-safe-p5`); fix what fails (likely spots: `InvWalCrashLaws`'s
  `walHistCerts_take` (`BigSepL.bigSepL_append` destructuring), `MemberCrash.lean`'s `memberDur_crash`
  pattern). Session 5's merge build was never finished either; this build covers it. **That build did not
  run**: lake refused the target list at once (`unknown target notes.mvcc-api-clients.ServerSpecs`: the list
  had three `notes.*` targets). Rerun with `$(cat /shared/tmp/p5-s6-leaves-nonotes.txt)` (157 leaves, the
  `notes.*` lines dropped) in place of the list above.
  **(b) plan under the alternative** (next session, in order):
  1. The contract over `walHistH`: `isWalStorage`'s `Save`/`SaveSnap` AUs become `AU <{ ∃∃ Hs, walHistH h Hs
     sized }> <{ walHistH h (Hs ++ [op]) sized, COMM Q Hs }>` (layer 1 needs no `WalSaveOk`/term premise:
     `walHistH_saveAU`/`walHistH_saveSnapAU` are the proofs in `RnNewStorage`); keep `walSaveSized_spec`/
     `walSaveSnapH_spec` (`WalApi.lean`) as derived laws over `walRecsH` by a conversion `AU_R ⊢ AU_H` (open:
     `walRecsH_iff_hist`; commit: the eager fold's step, as in `walRecsH_saveAU`), so `raftNode__start` and
     `RaftLoopFreeze` need not move in step 1. Only the error arm differs (it returns `AU_H`): its callers
     refute it by the batch size, check each. `walSaveH.law`/`walSaveSnapH.law` restated over `walHistH`.
  2. The body: `walHistH h Hs true ∗ ⌜walRead Hs = some σ⌝` in place of `walRecsH h (recsOf vk.1 σ) Hs true`
     (`recsOf` only for the pending received snapshot), `HistOkK` without `walCommitLeFrom walFresh Hs`.
  3. The pending batch's images (`crashOk`, `j > pos`) no longer `ImgOk vk.1.S vk.1.l σ` at the `Save`, but
     "for every committed log `L` that `vk.1.S` agrees with up to its commit (`DurAgrees`, `|L| = commit`),
     with the read's snapshot term in `L` (from its certificate), `ImgOk vk.1.S L σ`" (pure, quantified over
     `L`). Discharged with `L` from `raftState_logView` on the entered state: at *enter* (the view moves to
     `{v' with l := L}`; `monoListAuth` grows from `v'.l`, a prefix by `isCommittedLogLb_agree`), and in the
     crash law after `readyCrashEnter` (the post's `l := L`). Caution: `raftState_logView` is at `⊤`; the
     crash law runs at `E \ rnDurKN` and *enter* inside `iinv`: a masked variant (`↑N ⊆ E`) of it is needed
     (raft's file `DurableLogView.lean`, additive; or call it after closing the invariant at *enter*).
  4. The step laws' proofs (`InvWalCrashPure`, `InvWalCrashSteps`, `InvWalCrashLaws`) and
     `wal.restartOk`'s body; `raftNode__start`'s call sites if `rnDurK_save`/`rnDurK_enter`'s shapes change.
  5. Delete `walRecsH` once unused. Then P5-RESTART (the restart slot's certificates arrive through T10's
     `bootstrapCrashContract.law` pass-through).
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
