# etcdserver: --max-txn-ops does not bound the operations of a transaction with nested transactions

- **Status**: open (documentation; not filed).
- **Where**: `server/etcdserver/api/v3rpc/key.go`, `checkTxnRequest`/`checkRequestOp`; the
  flag's text `server/embed/config.go:620` ("Maximum number of operations permitted in a
  transaction."), the field's comment in `kvServer` ("Txn.Success can have at most 128
  operations, and Txn.Failure can have at most 128 operations").
- **What happens**: `checkTxnRequest(r, n)` bounds the widest of `Compare`, `Success`,
  `Failure` by `n` and checks each nested transaction with the budget `n - opc`: the bound is
  per level, so nesting multiplies it (up to about `3^(n/3)` operations; in practice the gRPC
  message size bounds a request). Reproduction (in package `v3rpc`, as the sibling issue's):

```go
// maxTxnOps bounds each level, not the total.
func TestProbeMaxTxnOpsNested(t *testing.T) {
	const max = 4
	inner := func() *pb.RequestOp { return txnOp(putOp("x"), putOp("y")) }
	r := &pb.TxnRequest{Success: []*pb.RequestOp{inner(), inner()}}
	err := checkTxnRequest(r, max)
	t.Logf("2 nested txns of 2 puts each (6 ops, 4 puts) with maxTxnOps=%d: %v", max, err)
	// deeper: budget 9, 3 nested per level
	var mk func(d int) *pb.RequestOp
	n := 0
	mk = func(d int) *pb.RequestOp {
		if d == 0 {
			n++
			return putOp("k")
		}
		n++
		return txnOp(mk(d-1), mk(d-1), mk(d-1))
	}
	top := &pb.TxnRequest{Success: []*pb.RequestOp{mk(2), mk(2), mk(2)}}
	err = checkTxnRequest(top, 9)
	t.Logf("%d operations with maxTxnOps=9: %v", n, err)
	if err == nil && n > 9 {
		t.Errorf("a transaction with %d operations passes maxTxnOps=9", n)
	}
}
```

  prints `39 operations with maxTxnOps=9: <nil>` (and 6 operations pass `maxTxnOps=4`).
- **Expected**: the flag's text says a transaction; the field's comment says per branch. Either
  the documentation says "per level of nesting", or the check counts nested operations.
- **How the proof handles it**: the checks' model (`v3rpc.opCheck`, `Defs.lean`) is the code's
  per-level budget; nothing in the proofs relies on a total bound.
- **Possible fixes**: document the per-level meaning, or pass the remaining total budget down.
- **Found**: 2026-10-12, the request path's unit 0 (the plan's suspect 7).
