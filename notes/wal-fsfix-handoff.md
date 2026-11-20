# wal-fsfix handoff

## START HERE (2026-11-20 z)

- Branch `wal-fsfix`, worktree `/shared/etcd-grove-walfsfix`, head `git log -1`. Pin 3afd77e35:
  `--packages=/shared/tmp/manifest-3af.json`. `.lake/build` seeded from wal-link's at lean 94ea36b029 (merged: c7b7c8d8f1).
- **The user's decisions of 2026-11-20** (questions.md, ledger "2026-11-20: the error-free open/rename specs need
  the paths to fit"): (1) member-name bound in `bootCfgFresh`, `PathFits` premises up the stack; (2) flock out of
  `NoIoErr` (NoMapLockErr covers it). Config-C runs recorded (noioerr.md session 9; both pass after 768dbff487).
- **Done, uncommitted-then-committed in the WIP commit after this handoff** (not yet built past `GooseLang/Ext/Fs`):
  - trusted text: `Premises.lean` (no `"Flock"` in `IoCovers`, docstrings), Go texts `premise_no_io_err.go`, `doc.go`;
  - `NoMapLockErr.lean`'s `noIoErr_noMapLockErr_keeps` back to "disjoint but open"; `NoIoErr.lean` Flock case gone;
  - new `GooseLang/Ext/Fs/PathFitsLemmas.lean` (`WinOk`, `DirFits`, `winOk_short`, `winOk_child`,
    `pathFits_child`, `pathFits_of_dirFits`; lean-check clean);
  - `NoErrSpecsOpenFile` (`hS : Sio.path p ∧ PathFits p`), `NoErrSpecsRename` (`hfit`): lean-check clean;
  - `os.OpenFile.specCreateS`'s error arm `¬ FsNoErr ∨ ¬ PathFits (child d b)` (Spec + Proof/os/OpenFileS.lean);
    bbolt `Open.spec`'s error arm the same (Spec + Proof `Open.wp_proof`, `openFileDb_shared`);
  - `InvBbolt.lean`: `fileHoldsF`/`nameAtF`/`fileFreeF` carry `PathFits path` (last conjunct); `bPath_join`,
    `fileAt_fileHolds` fixed; `newBackend.lean`'s `kvGlue_Open`, `Proof/os/Rename.lean` (`rename_fileNE` takes
    `hfit`) fixed; `StartFiles.lean`: `hok : ∀ b ∈ bs, NameOk b ∧ PathFits (child r b)`.
- **Also done (d78e350c1e and the commit after)**: mvccrand/mvccfull `Adequacy`, `Results`, `TopLevelRobustness`
  (Spec+Proof) take `Hrfit : Fs.DirFits r` (closed-statement change) with `mvccfullNames_len`; new
  `storage/WalLayoutFits.lean` (`memberDataDir_child`, `dirFits_memberDataDir`: name ≤ 200 → `DirFits`, lean-check
  clean); `bootCfgFresh`'s last conjunct `(∀ k, … utf8Valid k) ∧ Fs.DirFits cfg.DataDir'` (destructuring sites of
  `bootCfgFresh` need `.2.2.1` for the UTF-8 part now). `bootstrapContract` (a closed premise) thereby changes: its
  precondition gains `DirFits`, its `bootOk`'s `Hsfree` (`snapFreeAll` → `fileFree`) now carries `PathFits` of each
  snapshot path: list both in the land report.
- **Next (in order)**: build `GooseLang.Ext.Fs.*` (a run was queued on build-slot: log /shared/tmp/walfsfix/fsbuild.log), then `Proof.os.*`, bbolt `Open`,
  backend; then the producers of the name claims: (a) `start_fileHolds` callers: mvccrand/mvccfull `Adequacy`
  (+ their `TopLevelRobustness` Spec/Proof): new premise `Fs.DirFits r` (closed-statement change: report) and a
  length lemma for `mvccfullNames` (as `mvccfullNames_ok`); (b) the etcd examples' snapshot names
  (`snapFreeAll` in `InvBoot`'s `Hsfree`, produced in etcdstart, `Dir.lean`/`Alloc3`/...) and the backend path:
  `bootCfgFresh` gains `DirFits cfg.DataDir'` (form decided, questions.md), discharged in etcdstart from
  `memberDataDir name` with a name bound (≤ 200 bytes) in the examples' member premises (`AdequacyMembers` `ms`,
  concrete names elsewhere: `winOk_child (winOk_short …)`); `snapDBPath sd i` component is 29 bytes.
  Find what breaks with `etc/importers.py --uses fileHoldsF/nameAtF/fileFreeF/specCreateS/bootCfgFresh`.
- Then: full timed build, tcb --check --update (+ collections, interfaces), cut.specNoErr, rnNewStorageOk_holds,
  independent attack (fresh read-only subagent, axiom skill) on Premises.lean's flock change, PathFits and the
  new conjunct, STOP at the land stop listing old → new closed statements (mvccrand/mvccfull `Hrfit`, etcd examples'
  name bound, rnNewStorageOk gone). Create.specNoErr stays a STOP (directory read permission).
- Pitfalls: Go tests here as root; `/shared` idmapped; no loop devices here; SaveDBFrom's axiom now reads
  `fileFree`/`fileAt` with `PathFits` (same path in and out: no new claim; mention in the land report).

## History (2026-11-20 y)


- Branch `wal-fsfix`, worktree `/shared/etcd-grove-walfsfix`, head: `git log -1`. Pin 3afd77e35:
  `--packages=/shared/tmp/manifest-3af.json` (`.lake/package-overrides.json` = its copy). `.lake/build` seeded
  (cp -a) from wal-link's at lean 94ea36b029.
- c7b7c8d8f1 = merge of lean 94ea36b029 (wal-link landed). wal-link's split revert 28d300ba17 is NOT taken (the merge
  is of lean with that revert undone, so NoIoErr (a)/PathErrno stay). fb1fd2cef1 = the Fs repairs (NoIoErr.lean,
  NoMapLockErr.lean build, `lean-check -a`).
- **STOPPED (coordinator decision)**: lean's error-free open/rename specs (`NoErrSpecsOpenFile`: `open_failure_eintr`,
  `wp_osOpenCreateSNE`, `wp_osOpenFileSNE`; `NoErrSpecsRename`: `wp_osRenameFileSNE`) build `IoCovers "Open"/"Rename"`
  for ANY path; this branch's A1 decision covers only `PathFits` paths. Their callers (`Proof/os/OpenFileS.lean`,
  `Proof/os/Rename.lean`: `os.Rename.spec`, bbolt's `Open_sharedNoErr`, the server's snapshot backend) get paths from
  `memberDataDir name` with a generic `name`: a path-length fact must come from somewhere: a closed-statement
  premise (member names short) or a decision change. Options in the report (and below).
- Full timed build NOT run (would fail at NoErrSpecsRename/OpenFile and everything above them).
- Then: full build, tcb --check --update, collections, interfaces; cut.specNoErr (reuse `wp_osRenameFileSNE` etc.;
  `LockFile`'s blocking flock is named by both NoIoErr and NoMapLockErr now: a twin of trusted coverage, see report);
  rnNewStorageOk_holds; Create.specNoErr is a STOP (directory read permission, final attack finding 2).
- Config-C run at f5823538f2 done by the user (`/shared/tmp/walfsfix-cmodels/t.out`): the failures were harness
  bugs, fixed in 768dbff487 (Go/scripts only). Rerun for the user: commit 768dbff487, `examples/osfs/semantics/run-models-on-c.sh -v
  -run '^(TestNoIoErrPermissions|TestNoIoErrPermAncestor|TestNoIoErrPermFileWrite|TestNoIoErrProtectedSymlinks|TestDirRenameScopedToRoot|TestEnoent)$'`.
- Pitfalls: Go tests here as root; `/shared` idmapped; no loop devices in this container.

## History (2026-11-19 x)


- Branch `wal-fsfix`, worktree `/shared/etcd-grove-walfsfix`, head: `git log -1`. NOT merged with lean e95ce79ce9
  (pin 3afd77e35). Current pin f551a1b46: `--packages=/shared/tmp/manifest-f55.json`.
- Done: b65bc3e75c = the user's decisions on attack 7 (env clauses F1' no close during a lock call, F2' fd limits;
  F3' wording; nits; `env_no_close_during_lock.go`, `TestLocksCloseDuringLock`, `TestNoIoErrEmfile`). f5823538f2 =
  the final attack's findings recorded as known model gaps (noioerr.md session 8, notes/audit.md); no STOP.
- Full timed build of f5823538f2's Lean (same as b65bc3e75c): green, id 20261119-133559-4041148; no proof repair
  was needed (the LockStep/IoCovers changes of d1b49ad308 build).
- **STOPPED at the lean merge**: lean e95ce79ce9 (merge-origin4: origin's real bbolt, S3d `wp_logStepSWGQ`,
  `FsStep = FsStepV ∨ MmapStall`, `NoMapLockErr`, `NoErrSpecs{Open,OpenFile,Rename}`) conflicts in 55 files with
  wal-link's call-key change (`osCallS k s0 pc q`, `callKey R pc`) that this branch carries; origin's new bbolt and
  NoErrSpecs proofs use the old call API. Resolution belongs to wal-link's lean merge (aborted here). Resolved in
  the try: NoIoErr.lean (`fsStepV_of_ne` + `noIoErr_good`), Impl.lean's Mmap comment (both), TreeSharedStep/
  TreeSpecsMeta (HEAD + `hM`); TreeSharedLog/TreeSharedCreate need pc threaded through lean's Q variants.
- Next after the merge: tcb --check --update, collections, interfaces; cut.specNoErr (reuse lean's
  `wp_osRenameFileSNE` etc.: no twins), Create.specNoErr (needs directory READ permission in C's permissions
  first: final attack finding 2, a STOP), rnNewStorageOk_holds.
- Config-C run for the user: commit f5823538f2, filter
  `^(TestLocks|TestNoIoErr|TestDirRenameScopedToRoot|TestCrossRootRenameExcluded)` (report).
- Pitfalls: Go tests here as root; `/shared` idmapped (permission tests on /dev/shm); no loop devices in this
  container (run-models-on-c.sh must run on a host with them).

## History (2026-11-19 w)


- Branch `wal-fsfix`, worktree `/shared/etcd-grove-walfsfix`, head: see `git log -1` (merge of lean 1e4cb38613 on
  d1b49ad308). Pin f551a1b46: `--packages=/shared/tmp/manifest-f55.json`; `.lake/package-overrides.json` = its copy.
- Done: d1b49ad308 = the user's decisions of 2026-11-19 on the attack on 9017eb196d (LockStep option (b), NoIoErr
  blocking-only locks + `PathFits`, permission texts, A3 revert, Go examples/tests); noioerr.md session 7.
- **STOPPED at the independent attack** (noioerr.md, session 7, last section): refutation F1' (a blocking lock call
  succeeds after its fd's close), false texts F2' (EMFILE) and F3' (ENAMETOOLONG wording), nits. Decisions needed.
- NOT done: no Lean build yet over the new semantics (Impl.lean and TrustedCode/syscall.lean are imported by ~15k
  modules: a full timed build); `.lake/build` seeded from wal-link's (cp -a, 2026-11-19).
- Next after the decisions: fix the texts (each with Go example/measurement), re-attack if trusted text changes,
  full timed build (`/shared/tmp/build-slot.sh etc/timed-build.py --packages=/shared/tmp/manifest-f55.json`, run in
  background), repair bbolt/WAL proofs (expected mechanical: one conjunct fewer in LockStep's failure arm; IoCovers
  gains conjuncts), then cut.specNoErr (needs PathFits of the WAL paths: a dir-length premise), Create.specNoErr,
  rnNewStorageOk_holds (brief: wal-link's notes/wal-fsfix-brief.md).
- Pitfalls: df on /shared is tight (~30 GB free after the seed); Go tests here as root; `/shared` is idmapped
  (lchown → EOVERFLOW: run permission tests with SEMANTICS_C_DIR on /dev/shm); os.Chmod needs os.ModeSticky, not 0o1000.
