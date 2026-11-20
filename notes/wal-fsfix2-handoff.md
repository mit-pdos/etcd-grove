# wal-fsfix2 handoff

## START HERE (2026-11-20 a2) — item 2 for a fresh agent

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
