Title: etcdserver: fix data race on the alarm store when applying a snapshot

When applying a snapshot, [`restoreAlarms`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L2394-L2401) replaces `s.alarmStore` with a new store, unlocked, while [`Alarms`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L2425-L2427) reads it on gRPC and health-check goroutines. The lessor and the mvcc store are recovered in place under their own locks instead ([`lessor.Recover`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/lease/lessor.go#L600-L609)). This PR adds `AlarmStore.Recover`, which reloads the alarms from the new backend under the store's mutex, and calls it from `applySnapshot`. `NewServer` now builds the store itself, so `restoreAlarms`, whose only other caller it was, is removed.

Fixes #22653.

The first commit adds a test of the issue's example, which fails on `main` under `-race`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
