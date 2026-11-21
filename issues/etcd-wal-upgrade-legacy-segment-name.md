---
upstream: none
checked: 2026-11-20
links: []
blocks-proof: no
---

# The etcd fork cannot restart from a snapshot in a WAL written with older segment names

**Impact:** On upgrade, WAL recovery can report `ErrSnapshotNotFound` for a committed snapshot whose record is still present. The read starts too late because the older writer named a segment from the last entry even when a higher snapshot index had already appeared in a previous segment.

**Expected:** A member with the snapshot record and a contiguous WAL should recover its committed hard state and all entries following the snapshot. Its open file locks should protect the snapshot until a newer one is durable.

**Reproduction:** Replace the file of the same name in `server/storage/wal` of upamanyus/etcd at `d3feef9bc` with the test below. It writes snapshot 41 at commit 36 and closes the WAL before the hard state committing 41. On restart, the leader resends entries and the WAL cuts twice. The test gives those segments the filenames used by the older writer. The records are identical in the two layouts. The old layout produced `wal: snapshot not found` on the VM. [Go regression test](etcd-wal-upgrade-legacy-segment-name/segment_name_snapshot_test.go)

```sh
cd server
go test ./storage/wal -run '^TestUpgradeOldNamedWAL$' -count=1
```

**Cause:** A segment written by the old naming rule can sort at or below a snapshot recorded in a previous file. Filename selection starts scanning after the record and ReadAll reports it missing.

**Fix under verification** The reader locates the record in an earlier segment, validates the extended sequence and replays it, checking the term and CRC chain. The test checks commit 43, entries 42 and 43, read-only recovery, verification, retention of the lock protecting snapshot 41, and restart at snapshot 43 after purging the older segments. A truly absent snapshot still reports the established error. [Fork commit](https://github.com/upamanyus/etcd/commit/f6ef28518829ab1589fd24e7ed6693b5d5f36216)

## Proof

The existing WAL proof starts with files created by the verified writer. The Go regression exercises the upgrade layout separately. On the builder, the public ReadAll proof checks the new scanner against the filesystem and decoder. For files produced by the verified writer, a snapshot record in an older file has an index below the selected file’s starting index. The proof also follows the segment lock that the CRC seed identifies. The ReleaseLockTo proof checks against the nil-map correction proposed in [Perennial PR #645](https://github.com/mit-pdos/perennial/pull/645).
