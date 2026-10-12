# server/etcdserver/txn: a from-key delete then an ignore-value put in one transaction panics the apply loop

- **Status**: open (a reachable panic through the gRPC API; not filed).
- **Where**: etcd at bc8b52a50 (`etc/goose.py`'s etcd pin).
  - `server/etcdserver/txn/put.go:54-59`: `put` reads `prevKV.KVs[0]` for `IgnoreValue` and
    `IgnoreLease`, trusting its caller to have found the key.
  - `server/etcdserver/txn/txn.go:54` and `:201-228`: `Txn` checks every put of the chosen branch
    (`checkTxn` → `checkPut` → `checkAndGetPrevKV`) at its *read* transaction, before any
    operation runs.
  - `server/etcdserver/txn/txn.go:167-178`: `executeTxn` then runs the operations in order in the
    write transaction; `getPrevKV` re-reads the key there (after the operations before it) and
    `put` indexes the result.
  - `server/etcdserver/api/v3rpc/key.go:123-128, 236-315`: the gRPC layer's `checkIntervals`
    rejects a transaction whose put key overlaps a delete of the same branch ("duplicate key
    given in txn request"), but builds the delete's interval as
    `adt.NewStringAffineInterval(key, rangeEnd)`, and a from-key delete's `RangeEnd` is `"\x00"`
    (`clientv3.WithFromKey`, `client/v3/op.go:445-453`): the interval `[key, "\x00")` is empty,
    so it overlaps nothing.
- **What happens**: `Txn{Then: [DeleteRange{Key: "a", RangeEnd: "\x00"}, Put{Key: "a",
  IgnoreValue: true}]}` on a store where `"a"` exists passes `checkIntervals` and `checkTxn` (the
  key exists at the read transaction), deletes `"a"` in the write transaction, then `getPrevKV`
  finds nothing and `put` panics with `index out of range [0] with length 0`, inside the write
  transaction (its batch lock held). `IgnoreLease` instead of `IgnoreValue` panics the same way
  (`put.go:58`). In a server the panic is in the apply loop, on every member, for a committed
  entry: any client allowed to write the key can crash the cluster. (We did not test what a
  restarted member does with the entry.)

  Reproduction (two Go tests, run with `go test -overlay` in `/shared/etcd/server`):

  ```go
  // server/etcdserver/api/v3rpc/probe_key_test.go
  func TestProbeCheckIntervalsFromKeyDelete(t *testing.T) {
  	reqs := []*pb.RequestOp{
  		{Request: &pb.RequestOp_RequestDeleteRange{RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte("a"), RangeEnd: []byte{0}}}},
  		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("a"), IgnoreValue: true}}},
  	}
  	_, _, err := checkIntervals(reqs)
  	t.Logf("from-key delete + put: checkIntervals err=%v", err) // nil
  }

  // server/etcdserver/txn/probe_txn_test.go (next to txn_test.go's setup)
  func TestProbeDeleteThenIgnoreValuePut(t *testing.T) {
  	s, lessor := setup(t, testSetup{key: []byte("a")})
  	rt := &pb.TxnRequest{Success: []*pb.RequestOp{
  		{Request: &pb.RequestOp_RequestDeleteRange{RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte("a"), RangeEnd: []byte{0}}}},
  		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("a"), IgnoreValue: true}}},
  	}}
  	defer func() {
  		if r := recover(); r != nil {
  			t.Fatalf("Txn panicked: %v", r)
  		}
  	}()
  	Txn(context.TODO(), zaptest.NewLogger(t), rt, false, s, lessor, false)
  }
  ```

  Output: `from-key delete + put: checkIntervals err=<nil>` (with a point delete of `"a"` instead:
  `duplicate key given in txn request`), and `Txn panicked: runtime error: index out of range [0]
  with length 0`; the second test then hangs in its cleanup on the batch lock, as in
  `etcd-txn-empty-requestop.md`.
- **Expected**: the transaction fails with `ErrKeyNotFound` (as a put with `IgnoreValue` on a
  missing key does), or the gRPC layer rejects it as overlapping.
- **How the proof handles it**: the run's premise `IgnOk` (`Proof/go_etcd_io/etcd/server/v3/
  etcdserver/txn/TxnRun.lean`, in `OpsOk`): every put that needs the previous key-value finds it
  at the state it runs at, unless it was already missing at the read state (then `checkTxn`
  fails first). `executeTxn`'s spec takes the strong form, `Txn`'s (`TxnPre`) the weak one.
- **Possible fixes**: in `checkIntervals`, read a `"\x00"` range end as "every key from the key
  on" (`adt.NewStringAffineInterval(key, "")`, the affine infinity), which is the guard this case
  was meant to hit; and/or make `put` return `ErrKeyNotFound` instead of indexing an empty
  `KVs`. (An error in the write path still becomes `txn`'s `lg.Panic`, so the second fix alone
  only changes the panic's message: the check has to happen before the write transaction, e.g.
  `checkTxn` accounting for the branch's deletes.)
- **Found**: 2026-10-12, txn unit 3, stating `executeTxn`'s premises (`put` needs the key at the
  write transaction's state, `checkTxn` checks it at the read's); confirmed by the tests above.
