Title: etcdserver: fix data race on the alarm store when applying a snapshot

When applying a snapshot, [`restoreAlarms`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/server.go#L2394-L2401) replaces `s.alarmStore` with a new store, unlocked, while [`Alarms`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/server.go#L2425-L2427) reads it on gRPC and health-check goroutines. The lessor and the mvcc store are recovered in place under their own locks instead ([`lessor.Recover`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/lease/lessor.go#L600-L609)). This PR adds `AlarmStore.Recover`, which reloads the alarms from the new backend under the store's mutex, and calls it from `applySnapshot`.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main` under `-race`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
