Title: lease: persist all checkpoints of a request in one backend transaction

[`applierV3backend.LeaseCheckpoint`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/apply/backend.go#L99-L107) calls [`lessor.Checkpoint`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/lease/lessor.go#L367-L383) once per lease, and each call [persists its lease](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/lease/lease.go#L55-L61) under its own `LockInsideApply`. The [post-lock hook](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/server.go#L2448-L2455) sets the consistent index to the entry at the first of these locks, assuming the entry's writes are all under that lock, so a backend commit between two leases persists the index without the later leases. This PR makes `Lessor.Checkpoint` take the request's checkpoints and persist them under one lock.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
