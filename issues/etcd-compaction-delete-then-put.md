---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22376 issue open: same bug (compaction at a delete-and-recreate revision loses the live value)
  - etcd-io/etcd#22377 pr open: fix for #22376 (keyIndex.doCompact; a regression from #18274)
  - etcd-io/etcd#22395 pr open: related; closes the gRPC path to the bug (from-key delete then put in one txn)
---

# server/storage/mvcc: compacting at a revision that deletes a key and puts it again deletes the live value

- **Status**: open (not filed; no fix branch yet). Reachable through etcd's gRPC API (2026-10-14,
  below): `checkIntervals` rejects a transaction that deletes and puts one key only when the
  delete names the key or a bounded range; a from-key delete gets the empty interval
  ([etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md)), so
  `Then(OpDelete(k, WithFromKey()), OpPut(k, v))` is accepted. Also reachable through mvcc's own
  API (`store.Write`: `DeleteRange` then `Put` of a key in one write transaction).
- **Through the gRPC API** (2026-10-14, a single-member cluster built from upstream `main`
  f061acd09, `etcd` and `etcdctl` from `server/` and `etcdctl/`):

  ```
  etcdctl put 0 keep; etcdctl put a v1
  printf '\ndel a --from-key\nput a v2\n\n\n' | etcdctl txn    # SUCCESS, at revision 4
  etcdctl get a                                                # a = v2
  etcdctl compact 4 --physical                                 # compacted revision 4
  etcdctl get a     # the member exits: FATAL mvcc/kvstore_txn.go:128 "range failed to find
                    # revision pair" {"revision-main":4,"revision-sub":1}
  ```

  Restarted on its data directory, the member comes up and `etcdctl get a` returns `Count: 0`:
  the acknowledged `a = v2` is gone (the restored index has only the tombstone `(4, 0)`). Every
  member applies the compaction, so every member exits on its first read of the key. The
  `txn-delete-then-ignore-put` fix (a from-key delete read as `[Key, ∞)` in `checkIntervals`)
  rejects the transaction, so it closes this path too; mvcc's own API stays affected.
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
- **How it happens**: inside one revision, the delete writes a tombstone at `(c, 0)`, which
  closes the key's generation, and the put opens a new generation at `(c, 1)`. Compaction walks
  the generations from the oldest and stops at the first one whose tombstone is at or after
  `c`. That is the closed one, so it keeps the tombstone and never visits `(c, 1)`. The
  compaction job then deletes `(c, 1)` from the `Key` bucket, while the in-memory index still
  names it. In the gRPC reproduction above:

  1. `put 0 keep` is revision 2 and `put a v1` is revision 3: `a`'s generations are `{(3,0)}`.
  2. The txn is revision 4. The from-key delete of `a` writes the tombstone `(4, 0)` and the
     put of `a` writes `(4, 1)`: `a`'s generations are `{(3,0), (4,0)t}, {(4,1)}`. `get a`
     reads `(4, 1)` and returns `v2`.
  3. `compact 4`: `doCompact(4, available)` looks at the first generation, whose tombstone is
     `4 >= 4`, and stops there. `g.walk` marks `(4, 0)`, the generation's last revision at or
     below 4, available. `(4, 1)` is in the next generation and is not marked.
  4. The compaction job deletes from the `Key` bucket every revision at or below 4 that is not
     in `available`: `(3, 0)` and the live `(4, 1)`.
  5. `keyIndex.compact` trims the index to `{(4,0)t}, {(4,1)}`, so it still maps `a` to
     `(4, 1)` at every revision `>= 4`. `get a` asks the bucket for `(4, 1)`, finds nothing,
     and `rangeKeys` calls `lg.Fatal`: the member exits.
  6. On restart the index is rebuilt from the bucket, which holds only the tombstone `(4, 0)`:
     `get a` returns `Count: 0`, and the acknowledged `a = v2` is lost.

  ```go
  // server/storage/mvcc/key_index.go:258-282 (etcd main f061acd09)
  func (ki *keyIndex) doCompact(atRev int64, available map[Revision]struct{}) (genIdx int, revIndex int) {
  	// ...
  	f := func(rev Revision) bool {
  		if rev.Main <= atRev {
  			available[rev] = struct{}{}
  			return false
  		}
  		return true
  	}

  	genIdx, g := 0, &ki.generations[0]
  	// find first generation includes atRev or created after atRev
  	for genIdx < len(ki.generations)-1 {
  		if tomb := g.revs[len(g.revs)-1].Main; tomb >= atRev { // <- tomb == c == atRev: stop here
  			break
  		}
  		genIdx++
  		g = &ki.generations[genIdx]
  	}

  	revIndex = g.walk(f) // <- (c,1) is in the next generation: never marked available

  	return genIdx, revIndex
  }
  ```

  ```go
  // server/storage/mvcc/kvstore_compaction.go:58-64 (etcd main f061acd09)
  		keys, values := tx.UnsafeRange(schema.Key, last, end, int64(batchNum))
  		for i := range keys {
  			rev = BytesToRev(keys[i])
  			if _, ok := keep[rev]; !ok {
  				tx.UnsafeDelete(schema.Key, keys[i]) // <- deletes the live (c,1)
  				keyCompactions++
  			}
  ```

  ```go
  // server/storage/mvcc/kvstore_txn.go:125-129 (etcd main f061acd09)
  		revBytes = RevToBytes(revpair, revBytes) // <- the index still names (c,1)
  		_, vs := tr.tx.UnsafeRange(schema.Key, revBytes, nil, 0)
  		if len(vs) != 1 {
  			tr.s.lg.Fatal(
  				"range failed to find revision pair",
  ```
- **Expected**: compaction keeps, for every key, the revision a read at the compaction revision
  (or later) returns: here `(c, 1)`.
- **How the proof handles it**: the compaction model's theorem that a read at or above the
  compaction revision never names a revision compaction may delete (`named_not_del`,
  `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Compact.lean`, over `kiGet_avail`) needs the
  compaction revision's changes not to delete and then put one key (`NoDelPutAt`); without it the
  theorem is false, which is how the bug surfaced. Since the mvcc store's unit 6a (2026-10-13) the
  premise is `store.Compact`'s (and `compactLockfree`'s): its caller asserts `NoDelPutAt` of
  the revision it compacts at; the store records it (`crevSafe`) and every key the job deletes
  carries it (`delKey`), which is what lets the readers of a compacted store prove a read at or
  above the compaction revision unaffected (`rangeAnswers_not_del`). In the server it is the
  transaction checks' guarantee (`checkIntervals`, the txn package's `NoDupKeysPerRev`).
- **Possible fixes**: in `doCompact`, skip a generation whose tombstone is at `atRev` when a later
  generation has a revision at `atRev` (compare the next generation's first revision, not the
  tombstone, with `atRev`); or reject a put of a key the same write transaction deleted.
- **Found**: 2026-10-13, while proving the compaction model's coverage theorem (the mvcc store's
  unit 5a): the theorem is false without the premise.
