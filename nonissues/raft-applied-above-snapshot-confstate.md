---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---
# raft: a node restarted with `Config.Applied` above its storage's snapshot skips the configuration changes in between

`Config.Applied` is documented as "the last applied index": raft then returns no entry at or below
it and takes its configuration from `Storage.InitialState`'s `ConfState`, which for a
`MemoryStorage` is its snapshot's. An application that restarts with `Applied` above its snapshot
(its state machine durable past it) loses every configuration change in between: raft never hands
those entries out again, so the node runs with the snapshot's configuration (with voters `{1}` in
the snapshot and "add 2" at index 2, restarted with `Applied = 2`, node 1 elects itself alone).

**Why not an issue:** an unstated precondition of `Config.Applied` (the storage's `ConfState` must
be the configuration as of `Applied`) that etcd meets: it never sets `Applied` (`raftConfig`,
[server/etcdserver/bootstrap.go](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/bootstrap.go#L568-L580)),
so raft hands out every entry above the snapshot again. Documentation, at most
([`Config.Applied`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L147-L151):
"This is a very application dependent configuration"), or a check in `newRaft` that no conf change
lies between the snapshot and `Applied`.

`TestAppliedAboveSnapshotConfState` in
[`nonissues/raft-applied-above-snapshot-confstate/applied_above_snapshot_test.go`](raft-applied-above-snapshot-confstate/applied_above_snapshot_test.go)
(public `RawNode` API) fails at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64:

```
$ go test . -run '^TestAppliedAboveSnapshotConfState$' -count=1
--- FAIL: TestAppliedAboveSnapshotConfState (0.00s)
    applied_above_snapshot_test.go:32: voters map[1:{}] after restarting with Applied = 2: want 1 and 2 (entry 2 added voter 2)
    applied_above_snapshot_test.go:47: node 1 became leader without node 2's vote
FAIL
```

## Proof

no: `RestartNode.spec` takes `Applied` either `0` or within the stored log, and the storage's
`ConfState` the configuration at a point at or above `Applied`
(`Spec/go_etcd_io/raft/v3/RestartNode.lean`), which etcd (`Applied = 0`) and `examples/kvdurable`
meet.

## Notes

Found 2026-10-31 by a spec review of the durable node API (its `Applied` premise first allowed any
`Applied ≤ Commit`). The test shows the stale configuration, not two different entries committed
at one index (that needs three or more voters, with node 1 committing alone while the others,
which applied the changes, elect among themselves). The same test asserting the bug is
`examples/kvdurable/applied_test.go`. Upstream searched 2026-11-02 (`Applied ConfState restart`,
`Config.Applied`): nothing.
