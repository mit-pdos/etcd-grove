# wal-fsfix2 handoff

## START HERE (2026-11-20 a4) — item 2: WalA fields done (satL, fits, covP); next the cut proof

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
