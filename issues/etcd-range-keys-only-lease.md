# mvcc/txn: keys-only ranges return lease 0 unless sorted by value

- **Status**: open (a behaviour change of 7624a8a2e, 2026-05-25, "Range with --keys-only
  retrieves from memory when possible"; not filed).
- **Where**: `server/etcdserver/txn/range.go:67` at bc8b52a50 sets `FastKeysOnly: r.KeysOnly &&
  r.SortTarget != pb.RangeRequest_VALUE`; with it `storeTxnCommon.rangeKeys`
  (`server/storage/mvcc/kvstore_txn.go:90-105`) builds the key-values from the index alone: key,
  mod and create revisions, version, and no lease. A keys-only range sorted by value takes the
  full read (the value is needed to sort) and keeps the stored lease; `asembleRangeResponse`
  then clears only the value. The API documents `keys_only` as "returns only the keys and not the
  values" (`api/etcdserverpb/rpc.proto:486`), not as dropping the lease; before 7624a8a2e every
  keys-only range returned the lease.
- **What happens**: a key attached to lease 7, read keys-only: `Lease` is 0 when sorted by key (or
  not sorted), 7 when sorted by value. Reproduction (in `server/etcdserver/txn/`, next to
  `txn_test.go`'s `setup`):

  ```go
  func TestRangeKeysOnlyLeaseProbe(t *testing.T) {
  	s, _ := setup(t, testSetup{lease: 7})
  	s.Put([]byte("a"), []byte("v"), lease.LeaseID(7))
  	lg := zaptest.NewLogger(t)
  	for _, tgt := range []pb.RangeRequest_SortTarget{pb.RangeRequest_KEY, pb.RangeRequest_VALUE} {
  		resp, _, err := Range(context.Background(), lg, s, &pb.RangeRequest{
  			Key: []byte("a"), KeysOnly: true, SortTarget: tgt,
  		}, true)
  		if err != nil {
  			t.Fatal(err)
  		}
  		t.Logf("keys-only, sort target %v: key %q lease %d value %q", tgt, resp.Kvs[0].Key,
  			resp.Kvs[0].Lease, resp.Kvs[0].Value)
  	}
  }
  ```

  Output: `keys-only, sort target KEY: key "a" lease 0 value ""` and `keys-only, sort target VALUE:
  key "a" lease 7 value ""`.
- **Expected**: the same key-values whatever the sort target: either the lease always (as before
  7624a8a2e, and as the documentation suggests), or never.
- **How the proof handles it**: mvcc's fast read is `kvPtrIs false` (no value, lease 0); the
  server's model reads a key-value as `kvRead (fastKeysOnly o)`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/RangeModel.lean`), and the bridge to the client
  model's `rangeKvsOk` (`srvRangeOk_rangeKvsOk`, `range_rangeSel`) states the response as the
  client's key-values with the lease zeroed for a fast keys-only read (`leaseZ`).
- **Possible fixes**: keep the lease in the index-only path (the index does not hold it: the
  lessor's `GetLease(key)` does), or document that keys-only responses carry no lease and drop it
  in the value-sorted path too.
- **Found**: 2026-10-11, specifying `executeRange` against the client model (txn unit 2),
  confirmed by the test above.
