# wal-fsfix handoff

## START HERE (2026-11-19 w)

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
