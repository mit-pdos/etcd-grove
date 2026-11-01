---
upstream: unchecked
checked: 2026-11-01
links: []
---

# server/storage/mvcc: `HashStorage().Hash()` reads `currentRev` without `revMu`, racing with every write

- **Status**: a data race (Go's race detector reports it). The returned revision may not be the
  one the hash is of: the code's TODO says so ("hash and revision could be inconsistent"), but the
  read itself is unsynchronized, which Go's memory model does not define. Reachable through etcd's
  maintenance API (`Hash` RPC: `maintenanceServer.Hash` → `HashStorage().Hash()`) while the apply
  thread writes. (Also, by reading: `hash()` reads `s.b` without `s.mu`, which `Restore` replaces
  under it, so a `Hash()` during a snapshot's restore may hash the old backend; not reproduced.)
- **Where**: `server/storage/mvcc/kvstore.go:155-165` at the etcd pin (`etc/goose.py`,
  `249d76bea`): `store.hash()` returns `s.currentRev` with no lock. Every write transaction's
  `End` increments it under `s.revMu` (`kvstore_txn.go:214`); every other reader takes `s.revMu`
  (`Read`, `hashByRev`, `updateCompactRev`).
- **What happens** (reproduction, a test in a package importing mvcc; fails under `go test -race`
  at the pin, `WARNING: DATA RACE`, read at `kvstore.go:164` in `(*store).hash()`, previous write at
  `kvstore_txn.go:214` in `(*storeTxnWrite).End()`):

  ```go
  func TestHashConcurrentWrites(t *testing.T) {
  	lg := zap.NewNop()
  	bcfg := backend.DefaultBackendConfig(lg)
  	bcfg.Path = filepath.Join(t.TempDir(), "x.db")
  	be := backend.New(bcfg)
  	kv := mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
  	var wg sync.WaitGroup
  	wg.Add(1)
  	go func() {
  		defer wg.Done()
  		for i := 0; i < 200; i++ {
  			kv.Put([]byte("a"), []byte("v"), lease.NoLease)
  		}
  	}()
  	for i := 0; i < 50; i++ {
  		if _, _, err := kv.HashStorage().Hash(); err != nil {
  			t.Fatal(err)
  		}
  	}
  	wg.Wait()
  	kv.Close()
  	be.Close()
  }
  ```
- **Expected**: the revision read under `s.revMu`, as every other reader does (the TODO's own
  suggestion; or read it before the backend's hash, with `s.revMu.RLock`, which bounds it below).
- **How the proof handles it**: no spec of `hashStorage.Hash` is proved; the candidate
  `hashStorage.Hash.specC` (`notes/mvcc-api-candidate.md`) states the revision only as one the store
  had, and its proof would need the read synchronized (a racy read has no Iris proof).
- **Possible fixes**: `s.revMu.RLock(); rev := s.currentRev; s.revMu.RUnlock()` in `hash()` (one
  line; the inconsistency the TODO describes remains, but the race goes).
- **Found**: 2026-11-01, writing the candidate spec of `hashStorage.Hash` (the spec skill's
  iteration on mvcc's API); reproduced with the race detector.
