Title: etcdserver: count nested txns' operations toward --max-txn-ops

[`checkTxnRequest`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/key.go#L202-L231) checks `--max-txn-ops` per nesting level: each nested txn gets the limit minus its parent's operations, but its siblings each get the same budget, so a txn of 64 nested txns of 64 ranges passes a limit of 128. This PR counts the operations of every nested txn toward the limit; a request with at most one nested txn per level is checked as before.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
