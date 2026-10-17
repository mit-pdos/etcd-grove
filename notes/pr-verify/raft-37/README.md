# etcd-io/raft#37: tests and logs

Each test is in package `raft` and runs from the root of a raft checkout:
`cp <file> <checkout>/ && GOTOOLCHAIN=go1.27.1 go test -run <Name> -v .`

- **`rawnode_nonlocal_quorum_test.go`**
  - Runs against: the PR head `f353149418c6` (etcd-io/raft, gogoproto raftpb). It does not
    compile against the fork's protobuf-go v2 raftpb.
  - Contents: a hand-routed three-node cluster with `AsyncStorageWrites` and
    `AsyncStorageWritesNonLocalQuorum`, where a node's append thread can stall.
  - `TestNonLocalQuorumRestartAboveDurableLog` (finding 1): the leader applies entry 12 while
    its durable log and durable commit end at 11, and `NewRawNode` with `Applied = 12` panics.
  - `TestNonLocalQuorumFollowerAppliesUnstable` (finding 3): a follower applies an entry that is
    only in its unstable log.
- **`rawnode_nonlocal_quorum_test.log`**: the output of both tests at the PR head (both pass,
  which shows the behavior).
- **`rawnode_async_base_review_test.go`** (the reviewer's)
  - Runs against: the PR head. It needs `rawnode_nonlocal_quorum_test.go` beside it for the
    cluster helpers: `cp rawnode_nonlocal_quorum_test.go rawnode_async_base_review_test.go
    <checkout>/ && go test -run 'TestReview' -v .`
  - `TestReviewBaseAsyncRestartAboveDurableCommit`: the same restart panic with the option off.
    The entry is durable and only the `HardState` is stalled (finding 4).
  - `TestReviewNLQSnapshotAboveDurableLog`: `CreateSnapshot(applied)` panics (finding 2).
- **`rawnode_async_review_test.log`**: the output of the reviewer's tests at the PR head.

The reproduction of finding 4 against the pinned fork (`509271dac`, without the PR) is in
`issues/raft-async-applied-above-durable-commit/rawnode_async_restart_applied_test.go`.
