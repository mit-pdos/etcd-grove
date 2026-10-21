Title: server: check the gRPC quota against the current backend

The KV and lease gRPC servers check writes against a quota that [`newBackendQuota`](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/api/v3rpc/quota.go#L93-L95) builds once, when the servers are created, over the member's backend at that time. [`applySnapshot`](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/server.go#L1082-L1083) replaces that backend with the snapshot's and closes the old one, so the quota keeps measuring the closed backend; `applySnapshot` rebuilds only the [applier's quota](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/server.go#L1146-L1148). This PR builds the gRPC quota at each check, over the server's current backend.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
