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
  every later pass reads nothing (`last` is past the end) and still does not stop, force-committing
  the backend every `CompactionSleepInterval` (10 ms by default) until the store is closed. The
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
