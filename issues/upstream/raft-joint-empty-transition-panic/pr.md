Title: raft: refuse an empty joint conf change in a joint config

In a joint config, [`stepLeader`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1326-L1342) accepts any conf change with no changes, whatever its transition, as the one leaving the joint config. But [`applyConfChange`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1957-L1967) leaves only if [`LeaveJoint`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confchange.go#L111-L114) holds (`Auto` transition, no changes); otherwise it tries to enter a joint config again and panics with "config is already joint". This PR makes the leader accept a conf change in a joint config only if `LeaveJoint` holds.

Fixes #<issue>

`TestRawNodeProposeEmptyJointConfChange` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
