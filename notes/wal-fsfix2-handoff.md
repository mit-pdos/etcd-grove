# wal-fsfix2 handoff

## START HERE (2026-11-20 a8) — item 2 done (cut proved, one spec); item 3 STOPPED (needs `MarshalHsLaw`); land stop

- Worktree `/shared/etcd-grove-walfsfix2`, branch `wal-fsfix2`; pin c44b74871 (`--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`). lean `5e22c9a3b5` merged (`c20016562f`; conflict k8s/all `Adequacy.lean`:
  `hmsL` over both clusters, `k8s_compactorN.startAddrs_names_len` added). Full timed build and gates: see the report
  (`/shared/tmp/walfsfix2/full1.log`, `gates*.log`).
- **Done (48debd09fe, b3fb796306):** Preallocate witness (`preallocExtend`/`Preallocate` posts `err ≠ nil → ¬ FsNoErrIno`,
  `syscall.Fallocate.wp_grow` over `wp_osFallocFinishW`); `pipeErrW dir` (alloc, `pipeErrP`, `Open`, `wp_walPipeH_open`);
  **`cut.spec` one spec over `Sio`** (premises `walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)` and the room;
  instances `NoIoErr`/`NoMapLockErr`; error `err ≠ nil ∧ ¬ walCov Sio`), proved (`WAL__cut.lean`); `cut.specNoErr`,
  `walCov_cut`, `WAL__cutNoErr.lean` deleted; `sync.specCut` over `Sio`; `Save`/`SaveSnapshot`/storage `Save`/`SaveSnap`
  take the instance and the premise (`RnNewStorage` from `WalH.fits/covP/satL`); `fsStepSat_ioNoneL`; WAL and
  WalTester Links regenerated: `h_wal_WAL_cutNoErr` gone. Ledger: last 2026-11-20 entry. Forms: `questions.md` a8.
- **Item 3 STOP**: `rnNewStorageOk_holds` needs no `Create.specNoErr`; its `walStorSpecs h` needs the WAL's `Save`/
  `SaveSnapshot` linked at `walSrvP`, which take `h_WalPbIn_MarshalHsLaw walSrvP walSrvMr` (`pbutil.MustMarshalMessage`
  of a `*raftpb.HardState`), unproved: registering `raftpb.HardState` as a `PbTypeC` (as `pbEntryC`) needs a trusted
  encoder fact (`hsEncC_ok`, as `entryEncC_ok`): trust base. Proposal in the report. No closed statement changed.
- Next after the decision: item 3 per the decision (a linking module instantiating the storage proofs at every
  `WalH`, then `rnNewStorageOk` out of etcdstart's `commonPremises` and the examples' `Defs`).

## START HERE (2026-11-20 a7, superseded) — item 2, step (1) mostly done; next: Preallocate, pipeline, cut

- Worktree `/shared/etcd-grove-walfsfix2`, branch `wal-fsfix2`; pin c44b74871 (`--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`). lean NOT merged (now 951d520138; merge before the full build, seed
  nothing). `WAL__cut.lean` and the WAL `Link` still do not build (expected until step 3); all else targeted-built.
- **Option (A) approved by the user and done** (b744596bd8, trusted text, ledger third 2026-11-20 entry): `LockStep`
  takes the call (`self`) and a wait outcome (blocking request in conflict steps to itself); `ErrnoZero "OfdLock"`,
  `MapLockOk "Flock"` count the wait; `locks_blocking.go`/`doc.go`; lock calls no longer `FsRetOp`. Attack: no
  refutation (questions.md a6); its text gaps fixed. Go test for the user on C:
  `examples/osfs/semantics/run-models-on-c.sh -run 'TestLocksBlocking'` (not run by us).
- **Witnesses done** (questions.md "a6 forms"): OFD/flock lock calls (`wp_osOfdLockW`, `wp_osFlockW`,
  `NoMapLockErrSpecs.lean`), `FcntlFlock.wp_lock`, `Flock.spec`, `fileutil.lockPostW` (LockFile.spec,
  createNewWALFile.specLocked), shared opens (`wp_osOpenFileSW`, `NoErrSpecsTrunc.lean`: `wp_osOpenCreateSW`,
  `wp_osOpenTruncSW`), `os.OpenFile.wp_fileS`, `wp_truncS`, `specCreateTruncS(nc)`, `walOpen_tripleW`,
  `PipeLemmas.wp_createTmp` (error arm `tmpClaim ∗ ⌜¬ (FsNoErrOn (· = child dir b) ∧ PathFits (child dir b))⌝`).
  Witness form throughout: `W p := ¬ (FsNoErrOn (· = p) ∧ PathFits p)` (implies `¬ FsNoErrIno`'s refutation too).
- **Next, in order:** (1) `fileutil.Preallocate.spec` witness (over `FallocateAu`'s finish fact); `filePipeline.alloc`
  error arm with the witness (now dropped with `-` at `filePipeline__alloc.lean:83`). (2) pipeline: `pipeErrP`,
  `run.spec`/`Open.spec` error arms `¬ (DirFits dir ∧ FsNoErrOn (fun p => ∃ b, p = child dir b))`. (3) restate
  `cut.spec` (decided ONE-spec form, questions.md), delete `cut.specNoErr`/`walCov_cut`/`WAL__cutNoErr.lean`; rework
  `WAL__cut.lean`: step 8 via `walOpen_tripleW` + `LockFile.spec`'s `lockPostW`; errors refuted by
  `Fs.fsNoErrOn_of Sio` (`[FsStepSat (NoMapLockErr Sio)]` + premises). (4) Save/SaveSnapshot/storage/gen-link; item 3.
- Lean tips: `by tac` inside `⟨…⟩` swallows the comma: `(by …)`; no Mathlib (`swap`/`pick_goal`: use `rotate_left`);
  bare `isplitr` sends every hypothesis RIGHT, bare `isplitl` LEFT.

## START HERE (2026-11-20 a6, superseded) — STOP: the lock calls in `cut` cannot be witnessed; a5 below otherwise current

- Worktree `/shared/etcd-grove-walfsfix2`, branch `wal-fsfix2`; pin c44b74871 (`--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`). No Lean changed since a5 (0469050f3a); `WAL__cut.lean` and the WAL
  `Link` still do not build (expected until a5's step 3). lean not merged (at 951d520138 now).
- Recorded: etcd-grove-03's decision (the one-spec `cut.spec` form; witness approach accepted), `questions.md`.
- **Blocker** (ledger, 2026-11-20 third entry): `cut`'s two blocking `LockFile`s (pipeline's on `N.tmp`, step 8's after
  `newTail.Close()`) may fail under `NoIoErr`/`NoMapLockErr` when another description holds a conflicting lock
  (`LockStep` has no success then; the premises constrain only where a success exists), and no resource excludes a
  conflict (`lockCtx` tracks exclusive locks only while held). So `cut.spec`'s `¬ walCov Sio` error arm is unprovable.
  Proposal (A, trusted, recommended): a wait step for a blocking request in conflict, covered case "errno 0 or wait".
- After the decision: a5's steps (1)-(4) unchanged (with (A), the lock witness is `e ≠ 0 → ¬ FsNoErrIno` via a
  `ofdLock_noErr`/`flockBlock_noErr` over the new clauses).

## START HERE (2026-11-20 a5, steps still current) — item 2: cut's callees get error witnesses; then the cut proof

- Worktree `/shared/etcd-grove-walfsfix2`, branch `wal-fsfix2` (WIP commit 0469050f3a + handoff); pin c44b74871
  (`--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`). lean not merged since
  9d6a486a91 (lean is at d45f8b140e or later: merge before the full build). `WAL__cut.lean` and the WAL `Link` do
  NOT build now (callee specs changed under them): expected until step (3).
- **Design (forms decided, no trusted text):** a callee's error arm carries a witness that the file system can fail,
  `Fs.FsNoErrOn Ps` (`GooseLang/Ext/Fs/FsNoErr.lean`: `∃ Sio`, every inode, both premises, the paths `Ps`;
  `FsNoErrIno` = no path) as `bbolt`'s `¬ FsNoErr` does. The pipeline needs NO Sio threading: `pipeErrP`'s sent error
  will carry `⌜¬ (DirFits dir ∧ FsNoErrOn (children of dir))⌝`. `cut.spec` becomes ONE spec parametrized by `Sio`
  (as `Save.spec`): error arm `⌜err ≠ nil ∧ ¬ walCov Sio⌝`, premises `walCov Sio → DirFits dir ∧ ∀ b, Sio.path
  (child dir b)` and `walCov Sio → room ≤ maxBytes`, `[FsStepSat (NoMapLockErr Sio)]`; delete `cut.specNoErr` and
  `CalleeCov.walCov_cut` (no twins: report this form; the brief said "corollaries"). `Save`/`SaveSnapshot` get the
  `NoMapLockErr` instance and `⌜walCov Sio → DirFits dir ∧ covP⌝` (storage specs: from `WalH.fits/covP`).
- **Done (0469050f3a, lean-checked file by file; targeted build b1 green before the WriteAt part, b2 =
  `/shared/tmp/walfsfix2/b2.log`, green: Create, SaveSnapshot, cutPre, PreSync, WriteAt/WriteLong/Off, osfs, bbolt writeMeta/init, WalTester tryWrite):** witnesses on `os.File.Sync.specDirS`/`fileutil.Fsync.specDirS`
  (`wp_osDirSyncSW`), `os.File.Truncate.specAu` + `specWalTail` (`¬ FsNoErrIno ∨ maxBytes < tg`; `ResizeAu`'s
  `wp_osFtruncateFinish_au`/`wp_osFallocFinish_au` give `⌜e ≠ 0 → …⌝`, `NoIoErrResize.lean`), `os.Rename.specFileSnc/S`
  (`(err = nil → o.isSome) ∧ (err ≠ nil → ¬ (FsNoErrOn (· = child d' bt) ∧ PathFits … ∧ PathFits …))`,
  `wp_osRenameFileSW`), `syscall.Fdatasync.spec`/`fileutil.Fdatasync.spec`/`walPreSyncOk` (`¬ FsNoErrIno`),
  `specPreL`/`specPre` error arm `B ∨ (⌜¬ FsNoErrIno⌝ ∗ W)`, `WriteAt.specLong` (`wp_ino`, `wp_osPWriteFinishW`),
  `Write.wp_long`, `os.fileB`; `os.File.writerStreamINE` (PNE stream, `B ∗ ⌜¬ FsNoErrIno⌝`); `specPreL` and
  `saveState.specPre` now over `io.writerStreamPNE` (proofs over `flush.specPNE`, `encode.specGNE`: Link args change).
- **Next, in order:** (1) remaining witnesses: shared-mode open of an existing file (`os.OpenFile.wp_fileS`, `NsS.lean`;
  a `wp_osOpenFileSW` over `wp_osOpenFileSNE`, as `wp_osRenameFileSW`) and `specCreateTruncSnc` (alloc's create);
  the OFD lock (`syscall.FcntlFlock.wp_lock`: an `ofdLock_noErr` from `NoIoErr`'s `"OfdLock"` clause, blocking
  `F_OFD_SETLKW`) and the `flock` fallback (`flock_noErr`, `NoMapLockErr`); `fileutil.lockPost`'s error arm
  `∃ b, A x b ∗ ⌜b = true → ¬ FsNoErrIno⌝`; `createNewWALFile.specLocked`; `fileutil.Preallocate.spec` (over
  `FallocateAu`, whose finish now gives the fact). (2) the pipeline: `pipeErrP`, `alloc.spec`/`run.spec`/`Open.spec`
  error arms with `¬ (DirFits dir ∧ FsNoErrOn (fun p => ∃ b, p = child dir b))`. (3) `cut.spec` restated (above) and
  `WAL__cut.lean` reworked: `sync.specCut` at a call from `sync.spec`+`sync.specNoErr` (as `walCov_sync`), N.tmp writes
  via `writerStreamINE` + `saveCrc.specNE`/`encode.specGNE`/`saveState.specPre`, each error refuted by
  `Fs.fsNoErrOn_of Sio …`. (4) Save/SaveSnapshot/storage specs, `etc/gen-link.py --walfs` (and modes), item 3.
- Caution: `by tac, x` inside `⟨…⟩` swallows the comma: write `(by tac)`. In WAL spec files write `Fs.FsNoErrIno`.

## START HERE (2026-11-20 a4, superseded) — item 2: WalA fields done (satL, fits, covP); next the cut proof

- Worktree `/shared/etcd-grove-walfsfix2`, branch `wal-fsfix2`; pin c44b74871 (`--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`). Plain build-slot; lean-check `--max-open 2`. Decisions: `questions.md`.
- **Approved by the user 2026-11-20** and done: `WalA` (`storage/WalRecs.lean`; `WalH` extends it) gained `satL :
  FsStepSat (NoMapLockErr Sio)`, `fits : Fs.DirFits dir`, `covP : ∀ b, Sio.path (child dir b)`. Allocated at
  adequacy (`etcdWalArea`: `etcdFsExts_satL`, `dirFits_srvWalDirOf_memberDataDir` from the member name ≤ 200 bytes,
  `trivial` for `allIo`); `etcd_adequate_members`/`_alloc_members` take trailing `hmsL := by decide` (N variants:
  `startAddrs_names_len k`). Docstrings old → new: `WalA`, `wal.bootOk`, `walAreaFresh`. Ledger: the two 2026-11-20
  `cut.specNoErr` entries. Targeted builds green (27 adequacy modules, `RnNewStorage`); no full build yet.
- Attacks: both found no refutation (first satL/fits; second with covP, its text gaps fixed after build
  `b6.log`: docstring-only edits since, unbuilt). covP may be relied on.
- **Next, in order** (coordinator 2026-11-20): (1) one proof of `cut` parametrized by coverage (`WAL__cut.lean`:
  error arms `⌜err ≠ nil ∧ ¬ cov⌝`, callees at `CalleeCov.lean`'s "at a call" form), `cut.spec` (at `ioNone`) and
  `cut.specNoErr` (+ `satL`, `fits`, `covP` premises) corollaries; (2) the file pipeline: `filePipeline.Open`'s
  error comes from the background `alloc` (`filePipeline.run`), so `isFilePipe` must carry `Sio`/coverage/`DirFits`
  from `newFilePipeline` (Create, openAtIndex): **STOP if it needs more trusted text than covP**; (3) no-error callee
  specs (missing: truncate, fallocate, OFD lock; reuse `NoErrSpecsOpenFile`/`Rename`/`NoIoErrSpecs`/`NoMapLockErrSpecs`);
  callees with error arms in `cut`: Truncate, `sync.specCut`, pipeline Open, `saveCrc`, `encode.specG`,
  `saveState.specPre`, `sync.specPreL`, `Rename.specFileSnc`, `Fsync.specDirS`, `LockFile`; (4) Save/SaveSnapshot/
  storage specs/`gen-link`; (5) item 3 (`rnNewStorageOk_holds`; no `Create.specNoErr` expected). Merge lean when it
  moves. Land path and stops as in the brief.

## START HERE (2026-11-20 a3, superseded) — item 2 stopped: the WalH change needs path coverage too

- Worktree `/shared/etcd-grove-walfsfix2`, branch `wal-fsfix2`; pin c44b74871 (`--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`). Plain build-slot; lean-check `--max-open 2`.
- **Done (a3, uncommitted → committed as "wal-fsfix2 (2a)")**: the approved `WalH` change, as `WalA` fields (so
  `walAreaFresh`, allocated at adequacy, carries them and a faithful `bootstrap` can hand them on): `satL :
  FsStepSat (NoMapLockErr Sio)`, `fits : Fs.DirFits dir`. `fits` is NOT derivable from `bootCfgFresh`'s
  `DirFits DataDir` (the WAL directory is 3 bytes longer; bound 3800), so it comes from the member's name of at
  most 200 bytes at the areas' allocation: `dirFits_srvWalDirOf_memberDataDir` (`storage/WalLayoutFits.lean`),
  `walAreasFresh_boot`/`wp_walAreas`/`progOk_walAreas` take `∀ d ∈ Ds, DirFits (srvWalDirOf d)`,
  `etcd_adequate_members`/`_alloc_members` a trailing `hmsL : ∀ m ∈ ms, m.1.length ≤ 200 := by decide`
  (`walDirsFit_of_names`); N variants pass `startAddrs_names_len k` (new in each `Dir.lean`), k8s/all a split.
  `etcdFsExts_satL` (`FsExts.lean`). No closed statement changed.
- **STOP (the report)**: `cut.specNoErr` also needs the WAL directory's **paths** covered: `NoIoErr` covers `open`/
  `rename` only on `Sio.path p ∧ PathFits p`, and `WalA.cov` covers inodes only. Ledger entry "2026-11-20: `cut.specNoErr`
  also needs the WAL directory's paths covered" (proposal: `WalA.covP : ∀ b, Sio.path (child dir b)`).
- Independent attack on the WalH change: see the report / `questions.md`.
- **Next after the decision**: add `covP` (at adequacy `trivial`, `allIo`); then item 2 as planned below. Beware:
  the pipeline's `Open` error comes from the background `alloc` (`filePipeline.run`), so a no-error `Open` needs
  `isFilePipe` to carry `Sio`/coverage/`DirFits dir` from `newFilePipeline` (Create, openAtIndex): a ripple.
- Item 3 (`rnNewStorageOk_holds`): needs `walStorSpecs h` for every `WalH`, i.e. the storage specs linked, whose
  WAL `Save`/`SaveSnapshot` hang on `h_wal_WAL_cutNoErr` (WAL `Link.lean`); `Create` is not in it (bootOk is
  assumed), so no `Create.specNoErr` expected; to confirm once `cut` is linked.

## START HERE (2026-11-20 a2, superseded) — item 2 for a fresh agent

- Item 1 LANDED (lean 9d6a486a91, merged into this branch). Worktree `/shared/etcd-grove-walfsfix2`, branch
  `wal-fsfix2`; pin c44b74871 (`--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`);
  `.lake/build` is built at 94f2824169 (the lean merge is notes-only). Plain build-slot; lean-check `--max-open 2`.
- **Approved by the user 2026-11-20** (questions.md, ledger "2026-11-20: `cut.specNoErr` needs lock coverage…"):
  `WalH` (`storage/WalRecs.lean`, `WalA`'s fields; handed out by `wal.bootOk`, assumed) gains
  `FsStepSat (NoMapLockErr Sio)` and `Fs.DirFits dir` (the WAL directory's, derived from the data directory's
  `DirFits`). List old → new in the land report.
- **Do, in order:** (1) the `WalH` change, then an independent attack on it (fresh read-only subagent, axiom
  skill) BEFORE relying on it; (2) one proof of `cut` parametrized by coverage (error arms `⌜err ≠ nil ∧ ¬ cov⌝`,
  callees at `CalleeCov.lean`'s "at a call" form), `cut.spec` (at `ioNone`) and `cut.specNoErr` (+ the two new
  premises) as corollaries: no twins; (3) the no-error callee specs (below), reusing existing ones; (4) thread
  the premises through `Save`/`SaveSnapshot`/storage specs/`gen-link`; (5) item 3: if `rnNewStorageOk_holds` needs
  `Create.specNoErr`, STOP with a proposal. Hand off at ~300k.

## History (2026-11-20 a1) — item 1 at the land stop

- Verified at the commit after 553c3c21f4: full timed build `20261120-160035-816652` (+ `20261120-162415-882575`
  after comment-only fixes) green; `etc/gates.sh` all passed (tcb 674 axioms/2 sorries = baseline, no update;
  69 collections match; links, goose, gen-init, gen-raft-tla, copy-part, interfaces, api, tier 227, bounds 399,
  mode 456, axiom-tok, reader-slot 173, errorf-wrap, model-param, ...): `/shared/tmp/walfsfix2/gates1.log`.
- Independent attack on the restated texts: no refutation (`notes/wal-units/noioerr.md`, session 11).

- Branch `wal-fsfix2`, worktree `/shared/etcd-grove-walfsfix2` (off lean `cd4e31df13`). Pin c44b74871:
  `--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`. Plain build-slot.
  Decisions: `questions.md` (untracked, in the worktree).
- **Item 1 done** (553c3c21f4 and after): `config.snapDirOf d := path.joinModel [d, "member", "snap"]` (Go's
  `filepath.Join(d, "member", "snap")`; until now opaque); `Proof/path/CleanFits.lean` (`Clean` of a non-empty
  path lengthens nothing and keeps `Fs.WinOk`); `config/PathFits.lean` (`snapDirOf_fits`, `pathFits_snapDir_child`,
  `pathFits_backendPathOf`, `snapDirOf_cleanAbs`, `snapDirOf_under`); `snap.pathFits_snapDBPath`
  (`OpenSnapshotBackendLemmas`); texts: `config/Defs.lean` header, the `BackendPath` axiom's docstring,
  `bootCfgFresh`'s docstring; Go test `examples/etcd/snappaths` checks `SnapDir() == filepath.Join(d,"member","snap")`.
- Trusted meaning, old → new: (a) `BackendPath` axiom: returned `snapDirOf d ++ "/db"` for an unspecified function
  `snapDirOf` → returns `Clean(d/member/snap) ++ "/db"` (Go's string; snappaths test). (b) `bootstrapContract`/
  `bootOk` (closed premise): `isSnapshotter … (snapDirOf DataDir)`, `Hsdo`, `Hsfree`, `Hpath`, `Hbfile` now name
  Go's concrete directory; the `PathFits` in `Hsfree`/`Hpath` follows from the pre's `DirFits` (was asserted).
  No closed statement's text changed.
- Item 2 (`cut.specNoErr`) and item 3: see "Item 2 plan" below.

## Item 2 plan (`cut.specNoErr`)

- Callees whose error arms `cut`'s proof takes (`WAL__cut.lean`): `Truncate.specAu` (via `wp_specWalTail`),
  `sync.specCut`, `filePipeline.Open` (`walPipeH_open`: open-create + `Preallocate`), the header encodes on the new
  file (`saveCrc`, `encode.specG`, `saveState.specPre`: write errors), `sync.specPreL` (fdatasync),
  `os.Rename.specFileSnc`, `fileutil.Fsync.specDirS`, `fileutil.LockFile.spec` (OFD lock + flock fallback:
  `NoMapLockErr`). `Close`'s error is ignored. Low-level NE lemmas on lean: `NoErrSpecsOpenFile`
  (`wp_osOpenCreateSNE`, `wp_osOpenFileSNE`), `NoErrSpecsRename` (`wp_osRenameFileSNE`), `NoIoErrSpecs`
  (`wp_osFsyncNE`, `wp_osPWriteFinishKNE`), `NoMapLockErrSpecs` (`wp_osFlockNE`, `wp_osCloseNE`); missing:
  truncate, fallocate, OFD lock NE.
- Method (noioerr.md session 3's plan, no twins): parametrize `cut`'s proof by the coverage (error arms
  `⌜err ≠ nil ∧ ¬ cov⌝`, callees at the `CalleeCov.lean` "at a call" form), so `cut.spec` (at `ioNone`) and
  `cut.specNoErr` are corollaries of one proof.
- Premises to thread: `[FsStepSat (NoMapLockErr Sio)]` and `Fs.DirFits dir` reach `Save`/`SaveSnapshot` (their
  covered case), the storage specs and `WalH` (`walOpenWS` could carry `⌜walCov Sio → DirFits dir⌝`); the WAL
  directory's `DirFits` comes from the data directory's (`bootCfgFresh`).
  Caution: `WalH` (the open WAL's record, with `Sio` and its `FsStepSat (NoIoErr Sio)`) is handed out by
  `bootstrapContract`'s `wal.bootOk` (assumed), so a new field (the `NoMapLockErr` instance, the directory's
  `DirFits`) is a trusted-text change: a STOP before doing it.
- Item 3 (`rnNewStorageOk_holds`, `RnNewStorage.lean`): its `hS : ∀ h : WalH GF, walStorSpecs h` needs
  `WAL.Save.spec`/`SaveSnapshot.spec` linked for every `Sio`, i.e. `cut.specNoErr` proved (item 2); wal-fsfix's
  handoff also names `Create.specNoErr` (a STOP: directory read permission in C's model): to be confirmed when
  item 2 is done.
