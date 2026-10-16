---
upstream: unchecked
checked:
links:
---

# server/storage/mvcc: a negative `CompactionBatchLimit` makes every compaction loop forever

- **Status**: open (not filed; no fix branch yet).
- **Where**: `server/storage/mvcc` at bc8b52a50 (`etc/goose.py`'s etcd pin).
  `store.scheduleCompaction` (`kvstore_compaction.go:28-105`) deletes the compacted revisions in
  batches of `batchNum := s.cfg.CompactionBatchLimit` (line 47): each pass reads
  `tx.UnsafeRange(schema.Key, last, end, int64(batchNum))` (line 58) and ends the job when
  `len(keys) < batchNum` (line 68). The backend's range treats a non-positive limit as no limit
  (`backend/batch_tx.go:207-209`, `unsafeRange`: `if limit <= 0 { limit = math.MaxInt64 }`;
  `backend/read_tx.go:83-85` likewise). `NewStore` replaces only a zero limit by the default
  (`kvstore.go:91-93`), and the flag `--compaction-batch-limit` (`embed/config.go:739`, an
  unvalidated `fs.IntVar`; `CompactionBatchLimit` is passed through `embed/etcd.go:228` and
  `etcdserver/server.go:367`) accepts any integer.
- **What happens**: with a negative limit, the first pass reads every compactable revision at
  once, and since `len(keys) < batchNum` never holds for a negative `batchNum` the loop goes on:
  the later passes alternate between reading nothing and re-reading every kept revision (below),
  and never stop, force-committing the backend every `CompactionSleepInterval` (10 ms by
  default) until the store is closed. The
  finished-compaction mark is never written, the compaction hash is never stored, and the channel
  `Compact` returns is never closed (a caller waiting on it, as `etcdserver`'s compaction apply
  with `physical`, hangs). The next compaction is queued behind it on the FIFO scheduler and never
  runs. Reproduction (a test in `server/storage/mvcc`, run with `go test -run
  TestCompactionNegativeBatchLimit .`; it passes, i.e. confirms the behaviour, at the pin):

  ```go
  func TestCompactionNegativeBatchLimit(t *testing.T) {
  	for _, limit := range []int{0, -1} {
  		t.Run(fmt.Sprintf("limit=%d", limit), func(t *testing.T) {
  			b, _ := betesting.NewDefaultTmpBackend(t)
  			s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{},
  				StoreConfig{CompactionBatchLimit: limit, CompactionSleepInterval: time.Millisecond})
  			defer func() { s.Close(); b.Close() }()
  			for i := 0; i < 5; i++ {
  				s.Put([]byte("foo"), []byte(fmt.Sprint(i)), lease.NoLease)
  			}
  			ch, err := s.Compact(traceutil.TODO(), 4)
  			if err != nil {
  				t.Fatal(err)
  			}
  			select {
  			case <-ch:
  				if limit < 0 {
  					t.Fatalf("limit %d: expected the compaction never to finish", limit)
  				}
  			case <-time.After(2 * time.Second):
  				if limit >= 0 {
  					t.Fatalf("limit %d: expected the compaction to finish", limit)
  				}
  			}
  		})
  	}
  }
  ```

  Output: `limit 0: compaction finished`, `limit -1: compaction still running after 2s`.
- **How it happens**: the compaction job deletes compacted revisions in batches of
  `CompactionBatchLimit` and stops when a batch reads fewer keys than the limit. The backend
  reads a non-positive limit as "no limit", so with a negative limit every pass reads the whole
  range, and `len(keys) < batchNum` (a length below a negative number) is never true. The next
  pass starts after the last revision read, `rev`, but `rev` is declared inside the loop: a pass
  that reads nothing leaves it at zero and sets `last` back to the start of the key space. So
  the passes alternate between an empty read and a full scan of the kept revisions. With the
  reproduction above (`foo` put at revisions 2..6, `Compact(4)`, limit -1):

  1. Pass 1 reads revisions 2, 3, 4 (3 keys), deletes 2 and 3 and keeps 4 (the index keeps
     `foo`'s latest revision at or below 4). `3 < -1` is false, so `last` becomes `{4, 1}`, the
     job force-commits and sleeps.
  2. Pass 2 reads from `{4, 1}` to revision 5: nothing. `rev` is still `{0, 0}`, so `last`
     becomes `{0, 1}`, the start.
  3. Pass 3 reads from `{0, 1}`: revision 4 again (1 key). `last` becomes `{4, 1}`.
  4. Passes 2 and 3 repeat (an instrumented run reads 3, 0, 1, 0, 1, ... keys), each followed
     by a `ForceCommit` and a `CompactionSleepInterval` sleep, until the store is closed.
     `UnsafeSetFinishedCompact` never runs and the channel `Compact` returned is never closed.

  The job holds `LockForSafeRangeDelete` throughout, which also blocks a non-blocking
  defragmentation for good (this follows from the lock; not tested).

  ```go
  // server/storage/mvcc/kvstore_compaction.go:47-95 (excerpt) and kvstore.go:91-93 (etcd main f061acd09)
  	batchNum := s.cfg.CompactionBatchLimit
  	h := newKVHasher(prevCompactRev, compactMainRev, keep)
  	last := make([]byte, 8+1+8)
  	for {
  		var rev Revision // <- zero at every pass
  		// ...
  		keys, values := tx.UnsafeRange(schema.Key, last, end, int64(batchNum)) // <- no limit if batchNum <= 0
  		// ...
  		if len(keys) < batchNum { // <- never true if batchNum < 0
  		// ...
  		tx.Unlock()
  		// update last
  		last = RevToBytes(Revision{Main: rev.Main, Sub: rev.Sub + 1}, last) // <-
  		// ...
  		s.b.ForceCommit()
  // kvstore.go, NewStore
  	if cfg.CompactionBatchLimit == 0 { // <- a negative limit is kept
  		cfg.CompactionBatchLimit = defaultCompactionBatchLimit
  	}
  ```
- **Expected**: a non-positive limit either rejected at configuration (as other numeric flags are
  validated in `embed.Config.Validate`) or treated as the default (as `0` is), or as "no limit"
  with a loop that ends when a pass reads fewer keys than it asked for (none).
- **How the proof handles it**: the store's invariant `isStore` holds the configuration's two
  fields with `0 < CompactionBatchLimit` (the job's loop needs it to end, and the job's spec says
  so); `NewStore`'s spec takes `0 ≤ cfg.CompactionBatchLimit` as a premise (a zero limit is
  defaulted to 1000), `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/NewStore.lean`.
- **Possible fixes**: in `NewStore`, `if cfg.CompactionBatchLimit <= 0 { cfg.CompactionBatchLimit =
  defaultCompactionBatchLimit }`; or validate the flag in `embed.Config.Validate`.
- **Found**: 2026-10-13, while specifying the compaction job (`store.scheduleCompaction`, the
  mvcc store's unit 5a): its loop's exit needs a positive limit, which `NewStore` does not ensure.
