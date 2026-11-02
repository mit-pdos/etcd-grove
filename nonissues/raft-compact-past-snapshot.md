---
upstream: none
checked: 2026-11-01
links:
blocks-proof: no
---
# raft: compacting a `MemoryStorage` past its snapshot makes the leader panic when a follower lags

`MemoryStorage.Compact`'s documentation asks only that the compact index be at most the applied
index, but raft also needs the storage's snapshot to cover the compacted prefix: a leader serves a
follower behind the first index with `Storage.Snapshot()` and panics ("need non-empty snapshot")
if it is empty. With an older non-empty snapshot below the compact index instead, the leader would
send that stale snapshot again and again and the follower never catches up (not reproduced).

**Why not an issue:** a documentation gap (`Compact` and `Storage.Snapshot` do not state the
precondition) that etcd meets: etcd compacts only behind a snapshot it has just created
(`compactRaftLog`, server/etcdserver/server.go: `CreateSnapshot(snapi)`, then
`Compact(snapi - SnapshotCatchUpEntries)`); the test reaches the panic only through raft internals
(`newRaft`, a hand-set progress, `sendAppend`).

`TestCompactWithoutSnapshotPanics` in
[`nonissues/raft-compact-past-snapshot/compact_past_snapshot_test.go`](raft-compact-past-snapshot/compact_past_snapshot_test.go)
passes by recovering the panic at etcd-io/raft@c51f010c851e, go1.27.3:
`compact_past_snapshot_test.go:40: panic: need non-empty snapshot`.

## Proof

no: `MemoryStorage.Compact.spec` takes the premise that the compact index is at most the stored
snapshot's (`Spec/go_etcd_io/raft/v3/MemoryStorage__Compact.lean`), and the `Storage` contract
requires a non-empty snapshot once compacted (`HSnapshot`, `Proof/go_etcd_io/raft/v3/InvStorage.lean`);
etcd meets both.

## Notes

A documentation fix: say on `Compact` (and on `Storage.Snapshot`) that the snapshot must cover the
compacted prefix, or have `Compact` refuse an index past the snapshot's. Found 2026-10-26 by a
review of raft's public specs. Upstream searched 2026-11-01 (`Compact snapshot "need non-empty
snapshot"`, `MemoryStorage Compact snapshot panic`): nothing.
