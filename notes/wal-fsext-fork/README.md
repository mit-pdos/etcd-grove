# Fork commits for the WAL over fsExt (pushed 2026-11-14)

**Rebased and pushed 2026-11-16** (landing on `lean`): `lean` moved its etcd pin to `6e8f0c004` (restart3 A1,
`server/etcdserver/server.go` only), not an ancestor of `e115818f5`, so the six fixes (0001-0006) were rebased
onto it without conflicts: upamanyus/etcd branch **`goose-lean-walfs2`**, head
`8c28a4296f1699c699bc4d59459c691bcff995f0` (pseudo-version `v3.0.0-20261115085855-8c28a4296f16`), whose tree is
`e115818f5`'s plus `6e8f0c004`'s `server.go` change. `etc/goose.py` and the examples' `go.mod` pin it. The
branch `goose-lean-walfs` (`e115818f5`, on `2eaeb872b`) stays as it was (no force-push).

**Pushed** (the user's request, 2026-11-14) as upamanyus/etcd branch `goose-lean-walfs`, head
`3df9b265f7e7fd752cd85e7a8191a824f632313d`, on `2eaeb872b` (`lean`'s etcd pin, one `snap` commit past
`0b50f0426`): `2af9e3ec9` (0001), `313217f52` (0002), `e54378a5f` (0003), `594861caf` (0004), `3df9b265f`
(0005), then `e115818f5` (0006, 2026-11-15: `WAL.Sync` takes `w.mu`, the fix of the reproduced data race
`issues/etcd-wal-sync-releaselockto-race.md`, with its test; the user's decision: fork changes only for
demonstrated bugs). Head **`e115818f501dbc5987bf228740b76f26491eca1d`**, pseudo-version
`v3.0.0-20261115085855-e115818f501d`. `go test ./storage/wal/...` passes but for `TestWALByteMix`, which by design reports the synthetic
stale-old-byte mixes (808 and 50 wrong, 0 over zeros; `nonissues/etcd-wal-record-type-outside-crc.md`);
`./fileutil/...` passes. The pin moves to it when `lean` is merged (it pins `2eaeb872b`; `LinuxFs/` is gone
there: the per-byte file layer is back in the main tree, `003d52e8ff`).

Original text:

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
