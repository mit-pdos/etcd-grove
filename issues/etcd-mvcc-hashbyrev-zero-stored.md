---
upstream: unchecked
checked: 2026-11-01
links: []
---

# server/storage/mvcc: `HashByRev(0)` returns the hash stored by a compaction at revision 0, not the current revision's

- **Status**: a wrong result. `HashByRev(0)` means "the current revision" (`store.hashByRev`:
  `if rev == 0 { rev = currentRev }`), but `hashStorage.HashByRev` first returns any stored hash
  whose `Revision == rev`, and a compaction at revision `0` (accepted: `0 > compactMainRev = -1`)
  stores one with `Revision 0`. From then on `HashByRev(0)` answers with that hash (of revision 0,
  compact revision `-1`) instead of hashing at the current revision. Reachable through etcd's
  `HashKV` RPC with `revision = 0` (the latest) after a client's `Compact(0)`.
- **Where**: `server/storage/mvcc/hash.go:139-150` at the etcd pin (`etc/goose.py`, `249d76bea`):
  the stored-hash loop compares `rev == h.Revision` before `rev == 0` is resolved in
  `store.hashByRev` (`hash.go:162`); the job stores `KeyValueHash{Revision: 0}` after a compaction
  at `0` (`kvstore_compaction.go`, `scheduleCompaction`, through `s.hashes.Store`).
- **What happens** (reproduction, a test in a package importing mvcc; passes, confirming the
  behaviour, at the pin): three puts, `Compact(0)`, then `HashByRev(0)` returns `hash revision 0,
  compact revision -1, current revision 4, err <nil>`.

  ```go
  func TestHashByRevZeroAfterCompactZero(t *testing.T) {
  	lg := zap.NewNop()
  	bcfg := backend.DefaultBackendConfig(lg)
  	bcfg.Path = filepath.Join(t.TempDir(), "x.db")
  	be := backend.New(bcfg)
  	defer be.Close()
  	kv := mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
  	defer kv.Close()
  	for i := 0; i < 3; i++ {
  		kv.Put([]byte("a"), []byte("v"), lease.NoLease)
  	}
  	ch, err := kv.Compact(traceutil.TODO(), 0)
  	if err != nil {
  		t.Fatal(err)
  	}
  	<-ch
  	h, cur, err := kv.HashStorage().HashByRev(0)
  	t.Logf("HashByRev(0): hash revision %d, compact revision %d, current revision %d, err %v",
  		h.Revision, h.CompactRevision, cur, err)
  }
  ```
- **Expected**: the hash at the current revision (`Revision == currentRev`), as without a stored
  hash.
- **How the proof handles it**: the candidate `hashStorage.HashByRev.specC`
  (`notes/mvcc-api-candidate.md`) states the returned hash's revision as the one asked, or (for
  `0`) the current one: both, as the code does.
- **Possible fixes**: resolve `rev == 0` to the current revision before the stored-hash lookup, or
  skip stored hashes for `rev == 0`.
- **Found**: 2026-11-01, by the spec review of the candidate mvcc API (round 5, the
  `spec-reviewer` agent), reproduced with the test above. Related:
  `etcd-restore-scheduled-compact-zero.md` (another edge of a compaction at revision 0).
