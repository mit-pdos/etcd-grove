Title: etcdserver: send queued progress responses before a created response

`recvLoop` answers a progress request by queuing mvcc's progress response on the watch channel ([L395-L400](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/api/v3rpc/watch.go#L395-L400)), and a later create request by queuing the created response on `ctrlStream` ([L367](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/api/v3rpc/watch.go#L367)). `sendLoop` takes from the two in either order ([L435](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/api/v3rpc/watch.go#L435), [L514](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/api/v3rpc/watch.go#L514)), and the client [passes](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/client/v3/watch.go#L737-L738) a progress response arriving after the created response to the new watch, which it does not cover. This PR makes `sendLoop` send the responses already on the watch channel before a created response.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
