Title: server: close the old backend after the auth store moves off it

[`applySnapshot`](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/server.go#L1082-L1114) starts closing the old backend before `authStore.Recover` moves the auth store to the new one. Permission checks on gRPC goroutines ([`isOpPermitted`](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/auth/store.go#L879-L881), `CheckPassword`, `IsAdminPermitted`) read the auth store's backend, so in between they can lock a read transaction that the close has reset, and dereference a nil bolt transaction. This PR starts the close after `Recover` and `SetBackend`, and, since `Recover` replaces that backend without synchronizing with the checks (a race the new test reports under `-race`), makes `Recover` and the checks share a lock that a check holds until its read transaction is locked.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
