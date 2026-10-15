# server/storage/mvcc: `treeIndex.Compact` needs its calls not to overlap (an unstated precondition)

- **Status**: open (not filed; documentation only). Not reachable through mvcc's store: every
  call is in a compaction job (`store.scheduleCompaction`, `kvstore_compaction.go`), and the
  store's FIFO scheduler runs the jobs one at a time, in the order of their (increasing)
  revisions.
- **Where**: `server/storage/mvcc` at bc8b52a50 (`etc/goose.py`'s etcd pin). `treeIndex.Compact`
  (`index.go:205-228`) clones the tree under the lock, then, for each key index of the clone,
  takes the lock, compacts it (`keyIndex.compact`, `key_index.go:215-236`), deletes it from the
  tree **by key** if it is now empty, and unlocks. The `index` interface (`index.go:27-39`) says
  nothing of concurrent `Compact` calls.
- **What happens**: two overlapping passes. Pass B clones the tree; pass A empties key `k`'s key
  index and deletes it; `k` is put again (a new key index); pass B reaches the old key index from
  its clone and calls `compact` on an empty key index: `lg.Panic("'compact' got an unexpected
  empty keyIndex")`. Had the old key index not been empty, pass B's `tree.Delete(keyi)` (by key)
  could delete the new key index of `k`. Reproduction (a test in `server/storage/mvcc`, kept out
  of git as `.lake/go-src/etcd/server/storage/mvcc/zz_concurrent_index_compact_test.go`; it runs
  pass B's loop body by hand after pass A, the interleaving the lock allows):

  ```go
  func TestTreeIndexCompactOverlappingPasses(t *testing.T) {
  	lg := zaptest.NewLogger(t)
  	ti := newTreeIndex(lg).(*treeIndex)
  	ti.Put([]byte("k"), Revision{Main: 1})
  	ti.Tombstone([]byte("k"), Revision{Main: 2})
  	ti.Lock()
  	clone := ti.tree.Clone() // pass B's clone
  	ti.Unlock()
  	ti.Compact(3) // pass A: k's key index emptied and deleted
  	ti.Put([]byte("k"), Revision{Main: 4})
  	available := make(map[Revision]struct{})
  	clone.Ascend(func(keyi *keyIndex) bool { // pass B: index.go:212-226
  		ti.Lock()
  		defer ti.Unlock()
  		keyi.compact(ti.lg, 3, available) // panics: an empty key index
  		...
  	})
  }
  ```

  Output: `PANIC 'compact' got an unexpected empty keyIndex {"key": "k"}`. A pass at a lower
  revision after one at a higher revision does not panic but returns a map that is not what
  compaction at its revision keeps (the key indexes are already compacted above it).
- **Expected**: the `index` interface's `Compact` documented as not concurrent with itself, and
  its calls at nondecreasing revisions (what the store does).
- **How the proof handles it**: `treeIndex.Compact`'s spec takes the compactor's token
  (`idxCompactor γ c`, exclusive) with `c ≤ rev` and gives back `idxCompactor γ rev`
  (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/treeIndex__Compact.lean`); the index's lock
  invariant keeps the key indexes a pass has yet to visit in the tree (`idxCmpOwn`,
  `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvIndex.lean`). The store's proof (unit 5c) is to
  pass the token from job to job.
- **Possible fixes**: document it; or take the pass under a separate compaction mutex.
- **Found**: 2026-10-13, mvcc compaction unit 5b (the proof of `treeIndex.Compact`).
