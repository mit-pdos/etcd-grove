---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: no
---
# clientv3/leasing: a transaction with a nested transaction writes into the caller's `Op` slices

When a transaction through the leasing KV contains a nested transaction (`OpTxn` inside `Then` or
`Else`, or `Do` of such an `Op`), `gatherOps` runs `append(thenOps, elseOps...)` on the nested
`Op`'s own `thenOps` slice (`Op.Txn()` returns it, `OpTxn` keeps the caller's slice uncloned): if
that slice has spare capacity, the nested `elseOps` are written past its length into the caller's
array, which may back another slice of the caller, and concurrent commits sharing such an `Op` race.

**Why not an issue:** found by code reading, confirmed by a second reader; a precondition etcd
meets: its one caller, the gRPC proxy, builds every level with `make([]clientv3.Op, n)`
(`server/proxy/grpcproxy/kv.go`, `TxnRequestToOp`), with no spare capacity, so `append` allocates.
Code: [`gatherOps`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/util.go).

## Proof

no: the leasing contract takes the precondition (`opCapOk`, `opsCapOk`,
`Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean`), which the proxy's slices meet.
