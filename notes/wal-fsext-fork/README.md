# Fork commits for the WAL over fsExt (pushed 2026-11-14)

**Pushed** (the user's request, 2026-11-14) as upamanyus/etcd branch `goose-lean-walfs`, head
`594861caf8daea97b870cc04742e33192244492f`, on `2eaeb872b` (the etcd pin of `lean` then, one `snap`
commit past `0b50f0426`): `2af9e3ec9` (0001), `313217f52` (0002), `e54378a5f` (0003), `594861caf` (0004).
`go test ./storage/wal/...` passes but for `TestWALByteMix`, which by design reports the synthetic
stale-old-byte mixes (808 and 50 wrong, 0 over zeros; `nonissues/etcd-wal-record-type-outside-crc.md`);
`./fileutil/...` passes. The pin moves to it when `lean` is merged into the WAL branch (below).

Original instructions:

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
