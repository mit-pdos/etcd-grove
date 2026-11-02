---
upstream: unchecked
checked: 2026-11-02
links: []
---

# server/storage/mvcc: a progress request takes the two store locks in the wrong order, deadlocking with a write transaction's `End` and a waiting `Commit`/`Compact`

- **Status**: a deadlock (liveness) at mvcc's Go API. Not reachable through etcd's server as far as
  checked: the store's exclusive `store.mu` takers (`Commit`, `Compact`, `Restore`) run on the apply
  goroutine, which is also the only writer, so none waits while a write transaction is open. An
  embedder of mvcc that commits or compacts concurrently with writes and watch progress requests
  can hang.
- **Where**: at the etcd pin (`etc/goose.py`, `249d76bea`), `server/storage/mvcc/`:
  `watchable_store.go:59-60` documents that `watchableStore.mu` "should never be locked before
  locking store.mu". `progressIfSync` (`watchable_store.go:517-537`, through `RequestProgress` and
  `RequestProgressAll`) takes `s.mu.RLock()` and then `s.rev()` (`:507`, `s.store.Rev()`, the promoted
  `readView.Rev`, `kv_view.go:32-36`), which runs `store.Read`, taking `store.mu.RLock()`
  (`kvstore_txn.go:47`). A write transaction holds `store.mu.RLock()` from `Write` to `End`, and its
  `End` takes `watchableStore.mu.Lock()` (`watchable_store_txn.go`). With a third goroutine waiting
  in `store.mu.Lock()` (`Commit`, `kvstore.go`; `Compact`), Go's writer-preferring `RWMutex` blocks
  the progress request's `store.mu.RLock()`: the three wait on each other.
- **What happens** (reproduction; fails, 3 runs out of 3, at the pin):

  ```go
  func TestProgressCommitEndDeadlock(t *testing.T) {
  	lg := zap.NewNop()
  	bcfg := backend.DefaultBackendConfig(lg)
  	bcfg.Path = filepath.Join(t.TempDir(), "db")
  	be := backend.New(bcfg)
  	kv := mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
  	ws := kv.NewWatchStream()
  	id, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, 0) // synced
  	if err != nil {
  		t.Fatal(err)
  	}
  	tw := kv.Write(traceutil.TODO())
  	tw.Put([]byte("a"), []byte("1"), lease.NoLease)
  	go kv.Commit() // blocks on store.mu.Lock behind tw
  	time.Sleep(100 * time.Millisecond)
  	go ws.RequestProgress(id) // holds watchableStore.mu.RLock, blocks on store.mu.RLock
  	time.Sleep(100 * time.Millisecond)
  	done := make(chan struct{})
  	go func() { tw.End(); close(done) }() // blocks on watchableStore.mu.Lock
  	select {
  	case <-done:
  	case <-time.After(3 * time.Second):
  		t.Fatal("deadlock: the write transaction's End never returned")
  	}
  }
  ```

  (imports: `context`, `path/filepath`, `testing`, `time`, `go.uber.org/zap`,
  `go.etcd.io/etcd/pkg/v3/traceutil`, `go.etcd.io/etcd/server/v3/lease`,
  `go.etcd.io/etcd/server/v3/storage/backend`, `go.etcd.io/etcd/server/v3/storage/mvcc`.)
- **Expected**: the documented lock order holds; `RequestProgress` does not block a write's `End`.
- **How the proof handles it**: the specs are partial correctness (a WP rules out panics, not
  hangs), so no spec is falsified; mvcc's candidate API (round 10, `notes/mvcc-api-candidate.md`)
  says nothing of termination.
- **Possible fixes**: read the revision in `progressIfSync` without `store.mu`
  (`s.store.revMu.RLock(); rev := s.store.currentRev; s.store.revMu.RUnlock()`, as `watch` does), or
  read it before taking `s.mu`.
- **Found**: 2026-11-02, by the `spec-reviewer`'s review of mvcc's candidate API (round 10);
  reproduced the same day.
