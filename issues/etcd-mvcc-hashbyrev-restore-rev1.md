---
upstream: unchecked
checked: 2026-11-01
links: []
---

# server/storage/mvcc: `HashByRev` of a stored hash during `Restore` returns current revision `1`

- **Status**: a wrong result (a transient one). `store.Restore` resets `currentRev` to `1` (under
  `revMu`, holding `s.mu`) before it reloads the store from the new backend. `hashStorage.HashByRev`
  answers a revision with a stored hash by reading `currentRev` under `revMu` alone, without `s.mu`,
  so a call during a restore returns the stored hash with current revision `1`: the store's
  revision goes back to `1` in the reply, then forward again. Reachable through etcd's `HashKV` RPC
  (the header's revision) and the corruption checker's `HashByRev` while a member applies a
  snapshot (`applySnapshot` → `kv.Restore`).
- **Where**: `server/storage/mvcc/hash.go:139-148` (the stored-hash path: `s.store.revMu.RLock()`,
  `currentRev := s.store.currentRev`) and `kvstore.go:296-318` (`Restore`: `s.mu.Lock()`, then
  `currentRev = 1` under `revMu`, then `restore()`) at the etcd pin (`249d76bea`).
- **What happens** (reproduction, a test in a package importing mvcc; passes, confirming the
  behaviour, at the pin): five puts, a compaction at `3` (stores a hash of revision `3`), then a
  goroutine calling `HashByRev(3)` in a loop while the main goroutine calls `Restore` on the same
  backend 2000 times: `store at revision 6; lowest current revision HashByRev(3) returned: 1`.

  ```go
  func TestHashByRevDuringRestore(t *testing.T) {
  	lg := zap.NewNop()
  	bcfg := backend.DefaultBackendConfig(lg)
  	bcfg.Path = filepath.Join(t.TempDir(), "x.db")
  	be := backend.New(bcfg)
  	defer be.Close()
  	kv := mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
  	defer kv.Close()
  	for i := 0; i < 5; i++ {
  		kv.Put([]byte("a"), []byte("v"), lease.NoLease)
  	}
  	ch, err := kv.Compact(traceutil.TODO(), 3)
  	if err != nil {
  		t.Fatal(err)
  	}
  	<-ch
  	var stop atomic.Bool
  	var low atomic.Int64
  	low.Store(1 << 62)
  	var wg sync.WaitGroup
  	wg.Add(1)
  	go func() {
  		defer wg.Done()
  		for !stop.Load() {
  			if _, cur, err := kv.HashStorage().HashByRev(3); err == nil && cur < low.Load() {
  				low.Store(cur)
  			}
  		}
  	}()
  	for i := 0; i < 2000; i++ {
  		if err := kv.Restore(be); err != nil {
  			t.Fatal(err)
  		}
  	}
  	stop.Store(true)
  	wg.Wait()
  	t.Logf("store at revision %d; lowest current revision HashByRev(3) returned: %d", kv.Rev(), low.Load())
  }
  ```
- **Expected**: a revision the store had (the one before the restore, or after it), never the
  placeholder `1`.
- **How the proof handles it**: the candidate `hashStorage.HashByRev.specC`
  (`notes/mvcc-api-candidate.md`) takes a share of the store's open token, which `Restore` takes
  whole: the call and a restore do not overlap under the spec.
- **Possible fixes**: read `currentRev` in the stored path under `s.mu.RLock()` too (as
  `hashByRev` does), or have `Restore` not publish the placeholder (set `currentRev` once,
  after `restore()`).
- **Found**: 2026-11-01, by the spec review of the candidate mvcc API (round 5, the
  `spec-reviewer` agent), reproduced with the test above.
