Title: raft: do not restore a snapshot while applying committed entries

`Node` keeps stepping messages while the application applies a `Ready`'s committed entries ([`node.run`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/node.go#L394-L399)), so a follower can restore a snapshot then. [`restore`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1921-L1936) replaces the configuration with the snapshot's `ConfState`, which already reflects those entries' conf changes, and [`applyConfChange`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1951-L1971) applies the change it is given to the current configuration, so the application's `ApplyConfChange` applies such a change twice. This PR makes `restore` ignore a snapshot while `applying > applied`; the leader sends it again.

Fixes #<issue>

`TestRawNodeSnapshotDuringConfChangeApply` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
