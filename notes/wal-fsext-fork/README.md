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
- `0007` (wal-link, 2026-11-18, approved by the user via etcd-grove-03; pushed within `goose-lean-walfs3-fp` (the branch
  `goose-lean-walfs3` of the clone `/shared/tmp/wal-fork/etcd` was not pushed), head `f01ae14c9b95338efae4e2ac2d62703bc873d178`, on
  `8c28a4296`): `WAL.SaveSnapshot` checks the tail's offset after its record and cuts once it passes
  `SegmentSizeBytes`, as `Save` does (`cut` syncs the old tail first); before, it only synced. Why: the server
  saves a snapshot record from the apply thread once per applied batch past `SnapshotCount`, and raft hands a
  commit backlog out over `Ready`s with an empty hard state and no entries (whose `Save` writes nothing, so
  no cut), so the snapshot records between two entry-writing `Save`s grew one tail file without bound, up to
  ext4's `s_maxbytes` (`EFBIG`, the apply thread's `lg.Panic`); the proof could not bound them (layer 1's room
  budget, `nonissues/etcd-wal-savesnapshot-tail-efbig.md`). Test `TestSaveSnapshotCuts`
  (`server/storage/wal/savesnapshot_cut_test.go`): 64 snapshot records with no `Save` between them under a
  2 KiB segment size cut the tail (more than one file, the tail below the segment size) and the WAL opens at
  the last snapshot; it fails without the change (one file). `go test ./storage/wal/...` (GOWORK=off, go1.27.3, 32 min) passes but for
  `TestWALByteMix`, failing by design as at 0006 (the synthetic byte mixes, see above). `etc/goose.py` pins it (project `etcd`,
  translated with `--src etcd=/shared/tmp/wal-fork/etcd` until the push; the pin is now 0008's, below).
- `0008` (wal-link, 2026-11-18; **pushed by the user 2026-11-18** as upamanyus/etcd branch `goose-lean-walfs3-fp`,
  head `34dea163a76cc68a02e9a6ae1e86df0cec069be7`, on `f01ae14c9`): `SaveSnapshot` does not cut while `w.fp` is
  nil, i.e. in `Create`'s own call (before the file pipeline exists). Found while re-proving `SaveSnapshot`'s
  `Create` case: 0007 alone made a `Create` whose first segment (metadata and the empty snapshot) passes
  `SegmentSizeBytes` panic in `cut` (nil `w.fp`; reproduced with 65 MB of metadata, and in
  `TestCreateLargeMetadata`: 1 MiB under a 2 KiB segment size), where `8c28a4296` succeeded. The condition is
  `curOff < SegmentSizeBytes || w.fp == nil` (sync), else `cut`. `TestCreateLargeMetadata` fails at `f01ae14c9`
  (nil pointer) and passes at `34dea163a`; the WAL suite but the byte-mix tests passes (GOWORK=off, go1.27.3).
  `etc/goose.py` pins `34dea163a`; the examples' `go.mod`/`go.sum` are at its pseudo-version
  `v3.0.0-20261118203246-34dea163a76c` (`notes/wal-fsext-fork/bump-go-mod.sh`); `etc/goose.py --check` passes.
