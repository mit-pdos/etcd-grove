---
upstream: none
checked: 2026-11-11
links: []
blocks-proof: no
---

# wal: a transient ReadDir failure at startup can make etcd delete its WAL

`wal.Exist` returns false when `fileutil.ReadDir` fails for any reason (`EMFILE`, `ENOMEM`, `EIO`,
`EACCES`; [util.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/util.go#L30-L36)).
`bootstrap` takes that as "no WAL" (`haveWAL := wal.Exist(cfg.WALDir())`,
[bootstrap.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/etcdserver/bootstrap.go#L77))
and goes to `bootstrapNewWAL`, whose `wal.Create` checks `Exist` again
([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L103-L105)). If
that check fails too, `Create` builds a fresh WAL in `dir.tmp` and `renameWAL` runs
`os.RemoveAll(dir)` ([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L322-L325))
before renaming the fresh WAL into place: the member's hard state and entries are gone, and the member
comes up with an empty log over a backend that still holds its data. (If only the first check fails,
`Create` returns `os.ErrExist` and `bootstrapNewWAL` panics, which loses nothing.) The same at upstream
main (6974f522338b).

**Why not an issue:** found by code reading; the deletion needs two `ReadDir` failures on a directory
that exists, with the operations between them succeeding, and no test reaches it. The test in
[etcd-wal-exist-readdir-error-removes-wal/](etcd-wal-exist-readdir-error-removes-wal/)
(`TestExistReadDirError`, file descriptors exhausted) shows only the first step: at the pin
`b18c2d500` and at upstream main `Exist` of a live WAL is false when its directory cannot be read.

## Proof

no: fixed on the fork (`goose-lean-exist` `c90b03b56`, on `goose-lean` `b18c2d500`): `Exist`
returns false only when the directory holds no WAL file or does not exist, true on any other error;
`bootstrap` then takes the restart path and fails with an error, and `Create` returns `os.ErrExist`.
`wal.Exist`'s trust-boundary spec states the fixed behavior with no premise: false only when no WAL is
at the directory. Upstream candidate: branch `fix/etcd-wal-exist-readdir-error` (`a6afba76d`) in
`/shared/tmp/wal-spec/w3/upstream-etcd`, off main `6974f522338b`, with the test.

## Notes

Found by the W4a Freeze review (2026-11-11, the axioms lens, M3).
