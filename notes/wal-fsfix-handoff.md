# wal-fsfix handoff

## START HERE (2026-11-19 x)

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
