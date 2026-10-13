# server/storage/mvcc: compacting at a revision that deletes a key and puts it again deletes the live value

- **Status**: open (not filed; no fix branch yet). Not reachable through etcd's gRPC API, whose
  `checkIntervals` rejects a transaction that deletes and puts one key; reachable through mvcc's
  own API (`store.Write`: `DeleteRange` then `Put` of a key in one write transaction).
- **Where**: `server/storage/mvcc` at bc8b52a50 (`etc/goose.py`'s etcd pin).
  `keyIndex.doCompact` (`key_index.go:258-282`) picks the first generation, from the oldest,
  that is the last one or whose tombstone has `tomb >= atRev` (line 272), then keeps that
  generation's last revision at or below `atRev` (`g.walk`, line 279). `store.scheduleCompaction`
  (`kvstore_compaction.go:58-66`) deletes from the `Key` bucket every revision at or below the
  compaction revision that `treeIndex.Compact`'s `available` map does not hold.
- **What happens**: a write transaction at revision `c` that deletes key `k` (tombstone `(c, 0)`,
  which closes `k`'s generation and opens an empty one) and then puts it (`(c, 1)`, the first
  revision of the new generation) leaves `k`'s generations `{..., (c,0)t}, {(c,1)}`. A compaction
  at `c` stops at the first generation (`tomb = c >= c`) and keeps the tombstone `(c, 0)`; the
  live revision `(c, 1)` is not in `available`, so the bucket's entry for it is deleted, while the
  index still answers `(c, 1)` for `k` at every revision `>= c`. The next read of `k` finds no
  value for the index's revision and `rangeKeys` calls `lg.Fatal("range failed to find revision
  pair")` (`kvstore_txn.go:126-129`): the member exits. Reproduction (a test in
  `server/storage/mvcc`, run with `go test -run TestCompactDeleteThenPutSameRevision .`; it
  passes, i.e. confirms the behaviour, at the pin):

  ```go
  func TestCompactDeleteThenPutSameRevision(t *testing.T) {
  	b, _ := betesting.NewDefaultTmpBackend(t)
  	lg := zaptest.NewLogger(t, zaptest.WrapOptions(zap.WithFatalHook(zapcore.WriteThenPanic)))
  	s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
  	defer func() { s.Close(); b.Close() }()

  	s.Put([]byte("foo"), []byte("v1"), lease.NoLease) // rev 2
  	txn := s.Write(traceutil.TODO())                      // rev 3: delete then put
  	txn.DeleteRange([]byte("foo"), nil)
  	txn.Put([]byte("foo"), []byte("v2"), lease.NoLease)
  	txn.End()

  	r, err := s.Range(context.TODO(), []byte("foo"), nil, RangeOptions{})
  	if err != nil || len(r.KVs) != 1 || string(r.KVs[0].Value) != "v2" {
  		t.Fatalf("before compaction: %v %v", r, err)
  	}
  	ch, err := s.Compact(traceutil.TODO(), 3)
  	if err != nil {
  		t.Fatal(err)
  	}
  	<-ch
  	defer func() {
  		if p := recover(); p != nil {
  			t.Logf("after compaction at 3: the read panicked (lg.Fatal): %v", p)
  		}
  	}()
  	r, err = s.Range(context.TODO(), []byte("foo"), nil, RangeOptions{})
  	t.Fatalf("after compaction: read returned %v %v, expected the read to fail", r, err)
  }
  ```

  Output: `before compaction: foo = v2 at mod revision 3`, the compaction log line with
  `"number-of-keys-compacted": 2` (`(2, 0)` and the live `(3, 1)`), then `after compaction at 3:
  the read panicked (lg.Fatal): range failed to find revision pair`. A compaction at `c + 1` or
  later is correct (the tombstone's generation is then skipped). The hash's `keyIndex.keep` makes
  the same choice of generation.
- **Expected**: compaction keeps, for every key, the revision a read at the compaction revision
  (or later) returns: here `(c, 1)`.
- **How the proof handles it**: the compaction model's theorem that a read at or above the
  compaction revision never names a revision compaction may delete (`named_not_del`,
  `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Compact.lean`, over `kiGet_avail`) needs the
  compaction revision's changes not to delete and then put one key (`NoDelPutAt`); without it the
  theorem is false, which is how the bug surfaced. The compaction's own specs do not need it (the
  job deletes what `doCompact` does not keep: `KeyDel`); the premise is the readers' of a
  compacted store (none is specified yet: the store's readers are those of a store never
  compacted, `crevFrozen`), and in the server it is the transaction checks' guarantee
  (`checkIntervals`, the txn package's `NoDupKeysPerRev`).
- **Possible fixes**: in `doCompact`, skip a generation whose tombstone is at `atRev` when a later
  generation has a revision at `atRev` (compare the next generation's first revision, not the
  tombstone, with `atRev`); or reject a put of a key the same write transaction deleted.
- **Found**: 2026-10-13, while proving the compaction model's coverage theorem (the mvcc store's
  unit 5a): the theorem is false without the premise.
