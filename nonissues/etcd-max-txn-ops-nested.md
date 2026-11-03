---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/etcd#22134 pr merged: related, not this bug (costTxnReq ignored nested RequestTxn; the same per-level blind spot in a different check)
blocks-proof: no
---

# etcdserver: --max-txn-ops bounds each nesting level, not the transaction

`checkTxnRequest(r, maxTxnOps)` bounds the widest of `Compare`, `Success`, `Failure` and checks each
nested transaction with the remaining budget of its level, so nesting multiplies the bound: 39
operations pass `--max-txn-ops=9`.

**Why not an issue:** documentation only: the flag's help says "Maximum number of operations
permitted in a transaction", the code's comment says per branch; the gRPC message size bounds a
request in practice, and nothing relies on a total bound.

## Proof

no: the checks' model is the code's per-level budget (`v3rpc.opCheck`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Defs.lean`); no result relies on a total bound.

## Notes

`TestMaxTxnOpsNested` in
[`nonissues/etcd-max-txn-ops-nested/max_txn_ops_nested_test.go`](etcd-max-txn-ops-nested/max_txn_ops_nested_test.go)
(copied as `zz_max_txn_ops_nested_test.go` into `server/etcdserver/api/v3rpc`) fails at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (go1.27.3): `a transaction with 39 operations
passes maxTxnOps=9`. A fix would document the per-level meaning, or pass the remaining total budget
down.
