---
upstream: unchecked
checked: 2026-10-26
links: []
---

# raft: compacting a `MemoryStorage` past its snapshot makes the leader panic

**Status**: an unstated precondition (documentation). `MemoryStorage.Compact`'s documentation asks
only that the compact index be at most `raftLog.applied`. Raft also needs the storage's snapshot to
cover the compacted prefix: it serves a follower that lags behind the first index with the
storage's `Snapshot()`, and panics if that is empty. Neither `Compact` nor the `Storage` interface
says so. etcd is not affected: it compacts only behind a snapshot it has just created
(`compactRaftLog`, `server/etcdserver/server.go:2132-2150`: `CreateSnapshot(snapi)`, then
`Compact(snapi - SnapshotCatchUpEntries)`).

**Where** (etcd-io/raft v3.7.0 plus the fork's fixes, `c8217eb9`, `etc/goose.py`'s pin; the files
below are unchanged from v3.7.0):

- `storage.go:265-267`: "Compact discards all log entries prior to compactIndex. It is the
  application's responsibility to not attempt to compact an index greater than raftLog.applied."
  `Compact` (`:268-290`) does not touch `ms.snapshot`.
- `raft.go:624-629`: `maybeSendAppend` falls back to `maybeSendSnapshot` when `term(Next-1)` fails
  (`ErrCompacted` below the first index).
- `raft.go:672-681`: `maybeSendSnapshot` reads `r.raftLog.snapshot()` (the storage's `Snapshot()`)
  and panics with `"need non-empty snapshot"` if it is empty.
- The `Storage` interface's `Snapshot` documentation (`storage.go`) does not say that a storage
  whose `FirstIndex` is above 1 must return a non-empty snapshot covering `FirstIndex-1`.

**What happens**: an application that compacts within the documented bound but without (or past)
a snapshot crashes its leader as soon as a recently active follower needs a compacted entry. With
an older, non-empty snapshot below the compact index instead, the leader sends that stale
snapshot, after which the follower still needs entries that no longer exist; the leader sends it
the same snapshot again and the follower never catches up (not reproduced). Reproduction (package
`raft`, [raft-compact-past-snapshot/compact_past_snapshot_test.go](raft-compact-past-snapshot/compact_past_snapshot_test.go);
`go test -run TestCompactWithoutSnapshotPanics -v .` logs `panic: need non-empty snapshot`):
a two-voter leader over a `MemoryStorage` holding entries 1-5, all applied (`Config.Applied =
5`), compacted to 4 without a snapshot; follower 2 probing at `Next = 1`, recently active;
`sendAppend(2)` panics.

**Expected**: either the documentation states the precondition (compact only up to the
storage's snapshot index: call `CreateSnapshot` at or above the compact index first, as etcd
does), or `Compact` refuses a compact index past the snapshot's.

**How the proof handles it**: the `Storage` contract requires a non-empty snapshot once the
storage is compacted (`HSnapshot`, `Proof/go_etcd_io/raft/v3/InvStorage.lean:480-490`:
`σ.prev.index ≠ 0 → snapshot index ≠ 0`), and `MemoryStorage.Compact.spec` takes the premise
`ci ≤ σt.ss.index` (the compact index at or below the stored snapshot's,
`Spec/go_etcd_io/raft/v3/MemoryStorage__Compact.lean:53`).

**Possible fixes**: add the precondition to `Compact`'s documentation (and to the `Storage`
interface's `Snapshot`: non-empty, covering `FirstIndex-1`, once entries were compacted); or have
`Compact` return an error for `compactIndex > ms.snapshot.Metadata.Index`.

**Found**: 2026-10-26, by a review of raft's public specs (the `Storage` contract against
`MemoryStorage.Compact`'s documentation).
