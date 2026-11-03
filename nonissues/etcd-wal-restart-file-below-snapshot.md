---
upstream: none
checked: 2026-11-03
links:
blocks-proof: yes
---
# etcd: a member restarted at a received snapshot names its next WAL file below the snapshot, and a later restart can fail

A follower that installed a received snapshot at `k` above its log (its last entry below `k`) and
restarts opens the WAL at that snapshot's record. `ReadAll` sets the WAL's last index (`w.enti`)
from the entry records only, never from the start snapshot, so it stays below `k`. When the tail
file fills, `cut` names the next file after `w.enti + 1`, below `k`. A later restart's `wal.Open`
at `k` picks the last file named at or below `k` (`searchIndex`), which does not hold the snapshot
record, and locks only from there on: the file that holds the record is unlocked, and the server's
WAL purge (`purgeFile`, `MaxWALFiles` 5 by default) may remove it. The restart after that finds no
snapshot record (`ValidSnapshotEntries`), opens at index 0, fails to find a file for it, and
exits (`lg.Fatal("failed to open WAL")`).

**Why not an issue:** reached by a test of the WAL through the server's `serverstorage.Storage`
and its restart sequence (`recoverSnapshot`, `openWALFromSnapshot` copied), but with the segment
size set to 1 byte (`wal.SegmentSizeBytes`) in place of a tail file that reached 64 MB, and run
against the goosed fork, not upstream (whose `enti` code is the same; upstream opens at the last
snapshot record, here the received one too). Found by the `axiom` skill's review of the WAL API
candidate (2026-11-03). Upstream not searched (no GitHub access from the session).

`TestA4ReceivedSnapshotRestartCutsPurgeRestart` in
[`nonissues/etcd-wal-restart-file-below-snapshot/restart_cut_test.go`](etcd-wal-restart-file-below-snapshot/restart_cut_test.go)
(a module whose `go.mod` replaces etcd by a local checkout of the fork), go1.27.1, failed at the
fork's `ce3dbc097`: restart 3 "file not found which matches the snapshot index '0'"; it passes at
`323320bb8`.

**The fork's fix** (`323320bb8`, branch `goose-lean-walsnap`): `ReadAll` raises `w.enti` to the
start snapshot's index when it matches its record (`TestCutAfterRestartAtReceivedSnapshotNamesFileAboveIt`
in `server/storage/wal/wal_test.go` fails without it). The same commit makes `LatestSnapshotEntry`
(`MinimalEtcdVersion`'s reopen) take the highest record, as `recoverSnapshot` does
(`nonissues/etcd-wal-snapshot-record-order.md`), which removes a panic there (`ErrSliceOutOfRange`
reopening at the older record; reached only by a downgrade's check). Noted, not changed: `ReadAll`
in write mode overwrites `ErrSnapshotNotFound` with `newFileEncoder`'s result, so an `Open` at a
missing record succeeds silently.

## Proof

yes: the WAL's API (`walFiles`, made by `Close`) says a restart reads back the records; without the
fix a later restart may not read them at all.
