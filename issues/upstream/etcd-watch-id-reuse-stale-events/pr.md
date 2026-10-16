Title: v3rpc: do not send a canceled watcher's events to a new watcher with its ID

`sendLoop` takes mvcc's watch responses and the created and canceled responses in either order ([L433-L435](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/api/v3rpc/watch.go#L433-L435), [L514](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/api/v3rpc/watch.go#L514)). A canceled watcher's responses taken after its canceled response are buffered under its ID and sent with the next created response for that ID ([L470-L476](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/api/v3rpc/watch.go#L470-L476), [L534-L553](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/api/v3rpc/watch.go#L534-L553)), or sent directly if that ID was created again already. This PR makes a create wait until the canceled watchers' queued responses are taken, and drops those taken after their canceled response.

Fixes #<issue>

`TestV3WatchReuseCanceledID` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
