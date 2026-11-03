---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/etcd#8102 pr merged: related, not this bug (introduced nested txns; does not document when a nested guard is evaluated)
blocks-proof: no
---

# txn: a nested transaction's comparisons see the state before the outer transaction's operations

`Txn` evaluates every comparison, the nested transactions' included, at the transaction's read view
before any operation runs. So in `Then(Put(k, "x"), Txn(If(Value(k) == "x"), ...))` on a store where
`k` is `"b"`, the nested comparison is false and the nested transaction takes its `Else` branch.

**Why not an issue:** documentation only: either semantics is defensible, and the API
(`RequestOp.request_txn`, `clientv3.OpTxn`) says nothing about when a nested guard is evaluated; at
most a doc comment.

## Proof

no: the server's run takes every nested verdict at the read state, and `Txn`'s spec says so
(`srvOps`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/TxnRun.lean`); the client model is related
to it under `OpsStable`.

## Notes

Reproduced 2026-10-12 with a probe test next to `txn_test.go`'s `setup` (nested `Succeeded=false`);
not kept.
