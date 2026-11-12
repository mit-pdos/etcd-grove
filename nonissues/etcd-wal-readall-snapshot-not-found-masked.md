---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---

# wal: a write-mode ReadAll loses ErrSnapshotNotFound

`(*WAL).ReadAll` sets `err = ErrSnapshotNotFound` when no snapshot record matches the snapshot the
WAL was opened at, then, in write mode, overwrites `err` with `newFileEncoder`'s result
(`w.encoder, err = newFileEncoder(...)`, nil on success) and returns it
([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L576-L599)).
So `Open(dir, snap)` at a snapshot the WAL has no record of, followed by `ReadAll`, succeeds: it
returns the entries after the snapshot's index as if the snapshot were the WAL's, though the
WAL never recorded it (the hard state and the entries are then not known to be consistent with it).
`ReadAll`'s comment promises `ErrSnapshotNotFound` in that case. Read-only mode (`OpenForRead`)
creates no encoder and reports it. The same at upstream main (6974f522338b) and at the etcd pin
(`c90b03b56`).

**Why not an issue:** a precondition etcd meets. `bootstrap` opens the WAL only at a snapshot the
WAL lists: it reads `wal.ValidSnapshotEntries(dir)` and loads the newest snapshot file among those
(`LoadNewestAvailable`), so a record matches. The test in
[etcd-wal-readall-snapshot-not-found-masked/](etcd-wal-readall-snapshot-not-found-masked/)
(`TestReadAllSnapshotNotFound`, a WAL of entries 1-5 with no snapshot record, opened at (3,1)) fails at
`c90b03b56`: `ReadAll` returns no error and 2 entries.

## Proof

no: `(*WAL).ReadAll`'s trust-boundary spec (`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean`)
takes the premise that the opened snapshot is the newest valid one of the history
(`some s = walNewestPair (walValidSnaps …)`), which excludes this case; its docstring says so.

## Notes

Found by the W4a Freeze review's second round (2026-11-12, the fresh lens, m1). A one-line fix
(`if err == nil && !match { err = ErrSnapshotNotFound }` after the encoder) would make the
documented behavior true; not on the fork (no proof needs it).
