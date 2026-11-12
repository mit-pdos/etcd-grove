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

**Why not an issue:** a precondition etcd meets, but not for the reason first given here. `bootstrap`
opens the WAL at the newest snapshot `wal.ValidSnapshotEntries(dir)` lists, and VSE lists every
snapshot record in the directory, while `Open` reads only from the last file named at or below the
snapshot's index (`searchIndex`). A record VSE lists can therefore lie before the files `ReadAll` reads:
when an entry below the snapshot's index is saved after its record, a cut names the next segment
`enti+1` at or below the index, and `Open` at the (valid) snapshot starts in that segment
(`TestReadAllStartRecordBeforeOpenedFile`). The masked error then also leaves `w.enti` unraised, so a
later cut names a segment below the snapshot, and a later `Open` or `ReleaseLockTo` leaves earlier
records unlocked for the purge. etcd can reach the unmatched read: a follower that persists a received
snapshot's record and crashes before the hard state that commits it restarts at an older snapshot,
then saves the entries the leader re-sends below the snapshot's index after its record; once the
commit reaches the snapshot, the next restart opens a segment after its record
(`/shared/tmp/wal-spec/w4a2/tests/w4a2_forgotsnap_test.go`, seen once in the W4a.2 probe). There the
masked read happens to be right (the re-sent entries are at or below the start, so they truncate),
which is why this stays a nonissue for etcd; the unsound cases need histories etcd does not write (an
entry below a committed snapshot after its record and a lowered commit, or an index of 2^64-1). The test in
[etcd-wal-readall-snapshot-not-found-masked/](etcd-wal-readall-snapshot-not-found-masked/)
(`TestReadAllSnapshotNotFound`, a WAL of entries 1-5 with no snapshot record, opened at (3,1)) fails at
`c90b03b56`: `ReadAll` returns no error and 2 entries.

## Proof

no: fixed on the fork (`goose-lean-exist` `1aaca041c`, on `c90b03b56`): a write-mode `ReadAll`
returns `ErrSnapshotNotFound` when no record matched its start snapshot (the one-line fix after
`newFileEncoder`), with the two tests above. `(*WAL).ReadAll`'s trust-boundary spec
(`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean`) relies on it: its premise that the
opened snapshot is the newest valid one does not exclude an unmatched read (the earlier claim that it
did was wrong: WAL W4a.2, finding F-W4a2-2, `notes/decisions.md`), and without the fix its result
(`walReadCut` of the whole history) differs from Go's, and the purge bounds of `Open`, `ReadAll` and
`ReleaseLockTo` (`walReleasePos`) are unsound. With the fix every successful write-mode `ReadAll`
matched, and the spec needs no history premise. **Open (2026-11-12, for etcd-grove-81):** the fix
makes the etcd restart above fail (`ErrSnapshotNotFound`) where the masked read was right; a cut
that names its segment above every snapshot record before it would avoid both.

## Notes

Found by the W4a Freeze review's second round (2026-11-12, the fresh lens, m1). The wrong argument
("the premise excludes this case") was found by WAL W4a.2 (2026-11-12): Go tests
`/shared/tmp/wal-spec/w4a2/tests/w4a2_wrap_test.go` (`TestW4a2UnmatchedRestartUnlocksGuardedRecord`).
