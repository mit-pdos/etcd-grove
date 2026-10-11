# server/etcdserver/txn: `Txn` panics on a `RequestOp` with an empty oneof

- **Status**: open (a precondition the package's API does not state; not reachable through
  the gRPC API, which rejects such requests; not filed).
- **Where**: `server/etcdserver/txn/txn.go` at bc8b52a50 (`etc/goose.py`'s etcd pin):
  `newTxnResp` (`txn.go:105-133`) leaves `resps[i]` `nil` for a request whose `Request` oneof
  is unset (`default:` at `txn.go:129`); `executeTxn` reads `tresp.Responses[i].Response`
  (`txn.go:143`) before its type switch, whose `default:` (`txn.go:194`) is commented
  "empty union" as if such requests were skipped. `IsTxnReadonly` (`txn.go:352`) counts the
  op as a write (`GetRequestRange()` is `nil`), so `Txn` takes the write path: the panic
  happens inside the write transaction. The gRPC layer (`api/v3rpc/key.go:317-331`,
  `checkRequestOp`) rejects an empty op with `ErrGRPCKeyNotFound` before proposing, so a
  request from a client never gets here; the txn package's exported `Txn` states no such
  precondition.
- **What happens**: a nil-pointer dereference panic. Reproduction (run with `go test
  -overlay`, in `server/etcdserver/txn/`, next to `txn_test.go`'s `setup`):

  ```go
  func TestTxnEmptyUnionProbe(t *testing.T) {
  	s, lessor := setup(t, testSetup{})
  	rt := &pb.TxnRequest{Success: []*pb.RequestOp{{}}}
  	defer func() {
  		if r := recover(); r != nil {
  			t.Logf("Txn panicked: %v", r)
  		}
  	}()
  	Txn(context.Background(), zaptest.NewLogger(t), rt, false, s, lessor, false)
  }
  ```

  Output: `Txn panicked: runtime error: invalid memory address or nil pointer dereference`.
- **Expected**: either the empty op is skipped, as the `// empty union` comments in
  `newTxnResp`, `executeTxn` and `checkTxn` suggest (its response left empty), or `Txn`'s
  documentation states that requests must have been validated (`checkTxnRequest`).
- **How the proof handles it**: the request predicates give an empty oneof no denotation
  (`requestOpIs`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/Requests.lean`): a spec of
  `Txn` over `txnRequestIs rt t` covers only requests whose every op is a range, a put, a
  delete or a non-nil nested transaction.
- **Possible fixes**: in `executeTxn`, read `tresp.Responses[i].Response` inside the cases that
  use it (or `continue` on a `nil` response); or document the precondition.
- **Found**: 2026-10-11, writing the request denotations of the txn package (unit 0), confirmed
  by the test above.
