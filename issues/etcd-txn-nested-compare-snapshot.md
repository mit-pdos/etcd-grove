# server/etcdserver/txn: a nested transaction's comparisons see the state before the outer transaction's operations

- **Status**: open (documentation: the behavior is not documented; not filed).
- **Where**: etcd at bc8b52a50: `server/etcdserver/txn/txn.go:45-50, 241-255` (`Txn` computes
  every comparison's verdict, the nested transactions' included, with `compareToPath` at the
  read transaction, before any operation runs; `executeTxn` then follows the precomputed path).
  `api/etcdserverpb/rpc.proto` (`TxnRequest`, `RequestOp.request_txn`) says nothing about when a
  nested transaction's guard is evaluated.
- **What happens**: in `Txn{Then: [Put{k, "x"}, Txn{Compare: [Value(k) == "x"], Then: [Put{r,
  "then"}], Else: [Put{r, "else"}]}]}` on a store where `k` is `"b"`, the nested comparison is
  false: it reads `k` before the first put, and the nested transaction takes its `Else` branch.
  Reproduction (`go test -overlay`, in `server/etcdserver/txn/`, next to `txn_test.go`'s
  `setup`):

  ```go
  func TestProbeNestedCompareAtStart(t *testing.T) {
  	s, lessor := setup(t, testSetup{key: []byte("k")}) // k = "b"
  	nested := &pb.TxnRequest{
  		Compare: []*pb.Compare{{Key: []byte("k"), Target: pb.Compare_VALUE, Result: pb.Compare_EQUAL, TargetUnion: &pb.Compare_Value{Value: []byte("x")}}},
  		Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("r"), Value: []byte("then")}}}},
  		Failure: []*pb.RequestOp{{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("r"), Value: []byte("else")}}}},
  	}
  	rt := &pb.TxnRequest{Success: []*pb.RequestOp{
  		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("k"), Value: []byte("x")}}},
  		{Request: &pb.RequestOp_RequestTxn{RequestTxn: nested}},
  	}}
  	resp, _, err := Txn(context.TODO(), zaptest.NewLogger(t), rt, false, s, lessor, false)
  	if err != nil {
  		t.Fatal(err)
  	}
  	t.Logf("nested Succeeded=%v", resp.Responses[1].GetResponseTxn().Succeeded) // false
  }
  ```

  The gRPC layer accepts the request (`checkIntervals`: the puts are on different keys).
- **Expected**: either behavior is defensible (all guards of a transaction on one snapshot, or a
  nested guard on the state its position in the transaction sees), but the API should say which;
  a reader of `OpTxn` naturally expects the latter (the operations before it are visible to the
  nested transaction's own operations).
- **How the proof handles it**: the server's run (`srvOps`, `Proof/go_etcd_io/etcd/server/v3/
  etcdserver/txn/TxnRun.lean`) takes every nested verdict at the read state, and `Txn`'s spec is
  stated over it. The client model in this repository (`TxnOp.txn`, `applyTxnOp`,
  `Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean`) evaluates a nested transaction's comparisons
  on the state the operations before it left, which is not what etcd does (`notes/STATUS.md`,
  txn unit 3); `txn_runTxn` relates the two under `OpsStable` (the verdicts agree; in particular
  without nested transactions).
- **Possible fixes**: document the snapshot semantics on `RequestOp.request_txn` (and
  `clientv3.OpTxn`).
- **Found**: 2026-10-12, txn unit 3, relating `compareToPath`/`executeTxn` to the client model's
  `runTxn`; confirmed by the test above.
