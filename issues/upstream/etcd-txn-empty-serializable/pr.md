Title: etcdserver: serve a txn without operations linearizably

[`Txn`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/v3_server.go#L345-L352) skips the read index for a read-only txn when [`IsTxnSerializable`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/txn/txn.go#L338-L350) holds, assuming that the client asked for a serializable read. `IsTxnSerializable` checks only that every operation is a serializable range, so it holds for a txn without operations, which asks for nothing. This PR makes `IsTxnSerializable` false for a txn without operations.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
