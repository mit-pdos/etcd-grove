Title: raft: switch to a snapshot's configuration when it is applied

[`applyConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1943-L1963) applies the given change to the current configuration, assuming that configuration is the one just before the change. [`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1915-L1928) switches to a snapshot's configuration as soon as a follower steps the snapshot, even while the application is still applying a `Ready`'s committed entries ([`Node` steps messages meanwhile](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L394-L399)), so a conf change among those entries is applied again on top of a snapshot that includes it. This PR switches to the snapshot's configuration in [`appliedSnap`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L766-L770), once the application has applied the snapshot, so that the configuration changes in log order.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

With `AsyncStorageWrites`, the snapshot can still be applied before the older entries; #<other PR> fixes that, and the two PRs merge cleanly in either order. I can combine both fixes in one PR if you prefer.

Written with the assistance of generative AI; I reviewed and tested every change.
