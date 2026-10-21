Title: raft: switch to a snapshot's configuration when it is applied

[`applyConfChange`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1943-L1963) applies the given change to the current configuration, assuming that configuration is the one just before the change. [`restore`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1915-L1928) switches to a snapshot's configuration as soon as a follower steps the snapshot, even while the application is still applying a `Ready`'s committed entries ([`Node` steps messages meanwhile](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/node.go#L394-L399)), so a conf change among those entries is applied again on top of a snapshot that includes it. This PR switches to the snapshot's configuration in [`appliedSnap`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L766-L770), once the application has applied the snapshot, so that the configuration changes in log order. With `AsyncStorageWrites`, the snapshot could still be applied before the older entries, so `RawNode` hands nothing to the append thread until they are applied.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
