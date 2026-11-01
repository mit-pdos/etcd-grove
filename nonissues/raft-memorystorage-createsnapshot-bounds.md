---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---
# raft: `MemoryStorage.CreateSnapshot` panics outside an undocumented index range

`MemoryStorage.CreateSnapshot(i, ...)` panics when `i` is past the last index ("snapshot 2 is out
of bound lastindex(1)") and, for an `i` the storage has compacted but newer than its snapshot
(`Compact` does not move the snapshot), with a runtime "index out of range" where `Term` and
`Entries` return `ErrCompacted`. Its documentation states no range.

**Why not an issue:** a precondition etcd meets (it calls `CreateSnapshot` only with its applied
index, after the entries are persisted, and compacts only below its last snapshot); documentation
only (INDEX-reviewed.md's Plan: "Skip for now").

`TestMemoryStorageCreateSnapshotBelowCompaction` and `TestMemoryStorageCreateSnapshotPastLastIndex`
in
[`nonissues/raft-memorystorage-createsnapshot-bounds/memorystorage_createsnapshot_bounds_test.go`](raft-memorystorage-createsnapshot-bounds/memorystorage_createsnapshot_bounds_test.go)
fail at etcd-io/raft@c51f010c851e, go1.27.3: `Panic value: runtime error: index out of range
[18446744073709551614] with length 2` and `Panic value: snapshot 2 is out of bound lastindex(1)`.

## Proof

no: `MemoryStorage.CreateSnapshot.spec`
(`Spec/go_etcd_io/raft/v3/MemoryStorage__CreateSnapshot.lean`) takes the premise
`ss.index < i → prev.index ≤ i ≤ prev.index + |ents|`, which etcd meets.

## Notes

A fix would document `firstIndex()-1 ≤ i ≤ lastIndex()`, or return `ErrCompacted` below the
first index.
