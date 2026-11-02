---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---
# raft: a member added after the storage's latest snapshot is sent that snapshot forever

A leader sends a follower whose next entries are compacted away its storage's `Snapshot()`, and a
follower drops a snapshot whose configuration does not include it. A member added after the
storage's latest snapshot, once it needs entries below the first index (a newcomer always does),
is sent that snapshot, drops it, and is sent it again, until the application takes a newer
snapshot; when the configuration needs its vote (a second voter added to a one-voter cluster)
nothing commits, so the application never applies anything to take a newer snapshot from, and the
cluster is stuck for good.

**Why not an issue:** an unstated precondition on what the storage's snapshot covers (that it
includes every member the leader may send it to), which etcd meets: it replaces the metadata of
every snapshot raft sends by its applied index and configuration
(`createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)`,
[server/etcdserver/server.go](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/server.go#L995)),
so the snapshot a newcomer receives always includes it; and liveness only. Raft's
[`Storage.Snapshot`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/storage.go#L91-L95)
says only "the most recent snapshot", while
[`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1869-L1898)
drops one without the recipient ("should never happen") and
[`maybeSendSnapshot`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L666-L681)
sends it regardless. The same kind of documentation gap as
[`raft-compact-past-snapshot`](raft-compact-past-snapshot.md).

`TestStaleSnapshotLivelock` in
[`nonissues/raft-snapshot-without-recipient-livelock/stale_snapshot_livelock_test.go`](raft-snapshot-without-recipient-livelock/stale_snapshot_livelock_test.go)
(public `RawNode` and `MemoryStorage` API, a lossless in-memory network run step by step: a
one-voter cluster applies 11 entries, snapshots and compacts at 11, adds voter 2, proposes; the
control run snapshots right after applying the change) fails at etcd-io/raft@c51f010c851e
(2026-10-23), go1.27.3 linux/amd64:

```
$ go test . -run '^TestStaleSnapshotLivelock$' -count=1 -v
    stale_snapshot_livelock_test.go:127: fixSnapshot=true: snapshot at 11, leader applied 13 -> 14, newcomer applied 14
    stale_snapshot_livelock_test.go:127: fixSnapshot=false: snapshot at 11, leader applied 13 -> 13, newcomer applied 0
    stale_snapshot_livelock_test.go:22: the newcomer never caught up and the proposal never committed
--- FAIL: TestStaleSnapshotLivelock (0.01s)
FAIL
```

## Proof

no: liveness, outside the safety theorems; the examples' stores avoid it (`examples/kvreconf`'s
`Replica.run` snapshots after every conf change it applies; `examples/kv` adds no member).

## Notes

Found 2026-10-28 writing `examples/kvreconf`'s randomized test (a joint change whose incoming
voters were newcomers never committed again, and the automatic leave never happened); the copy
asserting the bug is `examples/kvreconf/livelock_test.go`. Fixes: document on `Storage.Snapshot`
that the snapshot must include the recipient (take one after a conf change adding a member, or
return `ErrSnapshotTemporarilyUnavailable` until one exists); in raft, `maybeSendSnapshot` could
treat a snapshot without the recipient as temporarily unavailable, which stops the useless sends
but does not unstick the cluster. Upstream searched 2026-11-02 (`snapshot recipient`, `snapshot
new node stuck`): nothing.
