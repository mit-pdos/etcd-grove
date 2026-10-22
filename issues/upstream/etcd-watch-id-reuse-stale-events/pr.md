Title: etcdserver: do not send a canceled watcher's events to a reused watch ID

`sendLoop` takes mvcc's watch responses and the created and canceled responses in either order ([L433-L435](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/api/v3rpc/watch.go#L433-L435), [L514](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/api/v3rpc/watch.go#L514)). It buffers a response whose watch ID is not announced until that ID's created response ([L470-L476](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/api/v3rpc/watch.go#L470-L476), [L538-L553](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/api/v3rpc/watch.go#L538-L553)), assuming, as its comment says, that the ID is "not yet announced". After a cancel ([L534-L537](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/api/v3rpc/watch.go#L534-L537)), the ID's queued responses are the canceled watcher's, and a new watcher with that ID receives them. This PR drops a canceled watcher's queued responses and, on a stream where the client has set a watch ID, makes a create wait until they are taken.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
