# Fork commits pending the user's push (WAL over fsExt)

On upamanyus/etcd, branch `goose-lean-walfs`, on the pin `0b50f0426`: apply with `git am notes/wal-fsext-fork/*.patch`.

- `0001`, `0002` fix the two blocks-proof nonissues `etcd-fileutil-filebufreader-stat-panic` and
  `etcd-wal-create-cleanup-panic` (`notes/wal-fsext-plan.md`, section 8).
- `0003` (`f7e99d7aa`, tests only): the byte-mix power-loss tests of
  `nonissues/etcd-wal-record-type-outside-crc.md`. Kept as a patch because `0004`'s regression test
  (`TestWALTypeTearStaleTmp`) builds on its helpers.
- `0004` (`6dff53e17`): `filePipeline.alloc` opens `N.tmp` with `O_TRUNC`, the fix of
  `nonissues/etcd-wal-record-type-outside-crc.md` (`notes/decisions.md`, "WAL over fsExt: `N.tmp` opened
  with `O_TRUNC`"), with `TestFilePipelineTruncatesStaleTmp` and `TestWALTypeTearStaleTmp` rewritten to
  assert the safe outcome (both fail before it, pass after).

After the push: bump the etcd pin in `etc/goose.py` to the branch's head and the examples' go.mod/go.sum.
Until then the part's WAL is translated from the local checkout (`etc/goose.py --project etcd --src
etcd=<checkout>`), and `goose.py --check` of etcd fails on these branches.
- `0005` (`0bc171ac1`, on `6dff53e17`; `wal-create22`, 2026-11-14): `Create` closes the
  parent with `pdir.Close()` after a failed fsync, not `dirCloser()`, which overwrote `perr` with the
  close's `nil` and made `Create` return `(nil, nil)` with no cleanup
  (`nonissues/etcd-wal-create-parent-fsync-nil-nil.md`). No regression test (an fsync EIO on a directory
  is not injectable in the package's tests).
