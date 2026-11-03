---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---

# txn: Txn panics on a RequestOp with an empty oneof

`txn.Txn` on a `TxnRequest` with an op whose `Request` oneof is unset takes the write path, leaves
the op's response nil in `newTxnResp` and dereferences it in `executeTxn`: a nil-pointer panic with
the batch lock held.

**Why not an issue:** a precondition etcd meets: the gRPC layer rejects an empty op before proposing
(`checkRequestOp`, `server/etcdserver/api/v3rpc/key.go`, `ErrGRPCKeyNotFound`), at any nesting
depth; only an in-process caller of `EtcdServer.Txn` or the applier could send one. The `// empty
union` comments in `txn.go` suggest the case was meant to be skipped.

## Proof

no: the request predicates give an empty op no meaning, and the gRPC check is proved to exclude it
(`v3rpc.checkRequestOp_nonempty`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Results.lean`).

## Notes

Reproduced 2026-10-11 with a probe test next to `txn_test.go`'s `setup` (`Txn` on
`TxnRequest{Success: []*pb.RequestOp{{}}}`): `runtime error: invalid memory address or nil pointer
dereference`, then a hang in cleanup on the batch lock; not kept.
