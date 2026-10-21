Title: raft: defer a snapshot received while applying committed entries

[`applyConfChange`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1943-L1963) applies the given change to the current configuration, assuming that configuration does not include it yet. [`restore`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1913-L1928) replaces the configuration with a snapshot's even while the application is applying a `Ready`'s committed entries ([`Node` steps messages meanwhile](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/node.go#L394-L399)), so a conf change among those entries is applied again on top of a snapshot that includes it. This PR makes a follower keep a snapshot that arrives while committed entries are being applied, and step it again once the application has applied them.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
