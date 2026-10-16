---
upstream: none
checked: 2026-10-16
links:
  - etcd-io/etcd#17331 issue closed: related, not this bug (ConcurrentReadTx's stale-cache path copies the buffer redundantly; closed not planned)
---

# `ConcurrentReadTx` reuses a read-buffer copy from before a commit: deleted keys come back, old values return

- **Status**: open (not filed).
- **Where**: `server/storage/backend/backend.go` at the etcd pin of `etc/goose.py` (`bc8b52a50`):
  `backend.ConcurrentReadTx` (the `txReadBufferCache`, keyed by `txReadBuffer.bufVersion`),
  `batchTxBuffered.Unlock` (`writeback` under `readTx.Lock`, then `readTx.Unlock`, then
  `commit`, which takes `readTx.Lock` again), `batchTxBuffered.unsafeCommit` and
  `readTx.reset` (the buffer is emptied for the new bbolt read transaction, but `bufVersion` is
  not changed; only `writeback` increments it).
- **What happens**: a write session that deletes a key `k` put (and written back) earlier in the
  same batch interval ends with `Unlock`: the write-back increments `bufVersion` to `v` (the read
  buffer still has `k`), `readTx` is released, and the commit (a pending delete forces it)
  resets the read buffer and opens a new bbolt read transaction without `k`. A
  `ConcurrentReadTx()` that runs between the two critical sections copies the buffer (with `k`)
  into the cache at version `v`. After the commit, `bufVersion` is still `v`, so every later
  `ConcurrentReadTx()` takes the cached copy as up to date and reads `k` from it, over a bbolt
  transaction in which `k` is deleted, until the next write-back changes the version. The window
  is a few instructions, but a reader running concurrently hits it at once.

  Reproduction (`server/storage/backend/cache_stale_test.go`; fails at the pin on the first
  trial with `the deleted key "foo" is read back by ConcurrentReadTx`; the same loop without the
  concurrent reader passes 20000 trials):

  ```go
  package backend_test

  import (
  	"sync"
  	"sync/atomic"
  	"testing"
  	"time"

  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  	"go.etcd.io/etcd/server/v3/storage/schema"
  )

  func TestConcurrentReadTxStaleCacheAfterDelete(t *testing.T) {
  	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
  	defer betesting.Close(t, b)

  	tx := b.BatchTx()
  	tx.Lock()
  	tx.UnsafeCreateBucket(schema.Test)
  	tx.Unlock()
  	tx.Commit()

  	key := []byte("foo")
  	for trial := 0; trial < 20000; trial++ {
  		tx.Lock()
  		tx.UnsafePut(schema.Test, key, []byte("bar"))
  		tx.Unlock() // written back into the read buffer

  		var stop atomic.Bool
  		var wg sync.WaitGroup
  		wg.Add(1)
  		go func() {
  			defer wg.Done()
  			for !stop.Load() {
  				rtx := b.ConcurrentReadTx()
  				rtx.RLock()
  				rtx.UnsafeRange(schema.Test, key, nil, 0)
  				rtx.RUnlock()
  			}
  		}()
  		tx.Lock()
  		tx.UnsafeDelete(schema.Test, key)
  		tx.Unlock() // write-back, then commit (a pending delete)
  		stop.Store(true)
  		wg.Wait()

  		rtx := b.ConcurrentReadTx()
  		rtx.RLock()
  		ks, _ := rtx.UnsafeRange(schema.Test, key, nil, 0)
  		rtx.RUnlock()
  		if len(ks) != 0 {
  			t.Fatalf("trial %d: the deleted key %q is read back by ConcurrentReadTx", trial, ks[0])
  		}
  	}
  }
  ```

  A second reproduction, deterministic (no concurrency): any commit that changes a key the read
  buffer holds leaves the cache stale, and the pre-commit hook does so at every commit (etcd's
  hook, `cindex`'s `UnsafeSave`, rewrites the consistent index and term in `Meta`). Here the
  hook writes `index`; a writer's write-back brings its value into the read buffer, a
  `ConcurrentReadTx` caches it, a `ForceCommit` runs the hook (a new value, committed) and
  resets the buffer without changing its version, and the next `ConcurrentReadTx` reads the old
  value (`server/storage/backend/cache_hook_test.go`; fails at the pin with
  `ConcurrentReadTx reads index "1", BatchTx reads "2"`):

  ```go
  package backend_test

  import (
  	"fmt"
  	"testing"
  	"time"

  	"go.etcd.io/etcd/server/v3/storage/backend"
  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  	"go.etcd.io/etcd/server/v3/storage/schema"
  )

  // The pre-commit hook writes the same key at every commit (as etcd's consistent index does).
  // A ConcurrentReadTx caches the read buffer, which has the hook's last value (written back by
  // the next writer); the next commit's hook writes a new value, the commit resets the buffer but
  // not its version, and the next ConcurrentReadTx reuses the cached copy: the old value.
  func TestConcurrentReadTxStaleCacheAfterHookCommit(t *testing.T) {
  	n := 0
  	cfg := backend.DefaultBackendConfig(nil)
  	cfg.BatchInterval, cfg.BatchLimit = time.Hour, 10000
  	cfg.Hooks = backend.NewHooks(func(tx backend.UnsafeReadWriter) {
  		n++
  		tx.UnsafeCreateBucket(schema.Test)
  		tx.UnsafePut(schema.Test, []byte("index"), []byte(fmt.Sprint(n)))
  	})
  	b, _ := betesting.NewTmpBackendFromCfg(t, cfg)
  	defer betesting.Close(t, b)

  	read := func() string {
  		rtx := b.ConcurrentReadTx()
  		rtx.RLock()
  		defer rtx.RUnlock()
  		_, vs := rtx.UnsafeRange(schema.Test, []byte("index"), nil, 0)
  		if len(vs) != 1 {
  			t.Fatalf("index not found")
  		}
  		return string(vs[0])
  	}

  	b.ForceCommit() // the hook puts index=1, committed; it stays in the write buffer

  	tx := b.BatchTx()
  	tx.Lock()
  	tx.UnsafePut(schema.Test, []byte("other"), []byte("x"))
  	tx.Unlock() // writes index=1 and other back into the read buffer

  	if got := read(); got != "1" { // caches the read buffer
  		t.Fatalf("index = %q, want 1", got)
  	}

  	b.ForceCommit() // the hook puts index=2, committed; the read buffer is reset

  	tx.Lock()
  	_, wv := tx.UnsafeRange(schema.Test, []byte("index"), nil, 0)
  	tx.Unlock()
  	if got := read(); got != string(wv[0]) {
  		t.Errorf("ConcurrentReadTx reads index %q, BatchTx reads %q", got, wv[0])
  	}
  }
  ```

  In etcd as shipped the only caller of `ConcurrentReadTx` is mvcc's `store.Read`, which takes
  it under `s.revMu` shared, and the store's own writers' `End` holds `s.revMu` exclusively
  around the batch `Unlock`; the sessions that delete without `s.revMu` are compaction's (on the
  `Key` bucket: the stale copy keeps compacted revisions, which the index no longer names) and
  other buckets' (lease, auth: mvcc does not read them); the hook writes only `Meta`, which mvcc
  does not read through `ConcurrentReadTx`. So no wrong mvcc result is known; the
  backend's `ConcurrentReadTx` is wrong on its own terms (the comment in `ConcurrentReadTx` says
  the copy "is guaranteed to be up-to-date").
  A third reproduction (2026-10-13, found proving mvcc's store over the backend, unit 5),
  deterministic, with no hook and no delete: a range of a safe-range bucket (`Key`) returns a
  key twice. A put written back into the read buffer is cached by a `ConcurrentReadTx`; any commit
  (`ForceCommit` here, the backend's periodic `run` commit in a server) moves it into bbolt and
  resets the read buffer without changing its version; the next `ConcurrentReadTx` takes the
  cached copy, which still has the key, over the new bbolt transaction, which has it too, and
  `UnsafeRange` of a range returns bbolt's entries followed by the buffer's
  (`server/storage/backend/cache_range_dup_test.go`; fails at the pin with
  `range returned 2 keys (["k1" "k1"]), want 1`):

  ```go
  package backend_test

  import (
  	"testing"
  	"time"

  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  	"go.etcd.io/etcd/server/v3/storage/schema"
  )

  func TestConcurrentReadTxRangeDuplicateAfterCommit(t *testing.T) {
  	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
  	defer betesting.Close(t, b)

  	tx := b.BatchTx()
  	tx.Lock()
  	tx.UnsafeCreateBucket(schema.Key)
  	tx.Unlock()
  	b.ForceCommit()

  	tx.Lock()
  	tx.UnsafeSeqPut(schema.Key, []byte("k1"), []byte("v1"))
  	tx.Unlock() // written back into the read buffer

  	rtx := b.ConcurrentReadTx() // copies the read buffer into the cache
  	rtx.RLock()
  	rtx.RUnlock()

  	b.ForceCommit() // k1 into bbolt; the read buffer reset, its version unchanged

  	rtx = b.ConcurrentReadTx() // the cached copy (with k1) over the new bbolt transaction
  	rtx.RLock()
  	ks, _ := rtx.UnsafeRange(schema.Key, []byte("k0"), []byte("k9"), 0)
  	rtx.RUnlock()
  	if len(ks) != 1 {
  		t.Fatalf("range returned %d keys (%q), want 1", len(ks), ks)
  	}
  }
  ```

  mvcc's `store.Read` reads its `ConcurrentReadTx` one revision key at a time (`limit` 1: the
  buffer's entry, then no bbolt read), so no wrong mvcc result is known from this either; the
  watchable store's ranges use the shared `ReadTx`, which a commit updates under its lock.
  The proof's contract of mvcc's backend promises no range read of a `ConcurrentReadTx`
  (`keyReadSnap`'s `rng = false`).
- **How it happens**: the backend keeps recent writes in a read buffer on top of bbolt, and a
  reader sees bbolt's last committed transaction plus that buffer. `ConcurrentReadTx` gives each
  reader its own copy of the buffer. To save copies it caches the last copy, tagged with the
  buffer's `bufVersion`, and reuses it while the version is unchanged. Only `writeback`
  increments the version. A commit empties the read buffer, because its contents are now in the
  new bbolt transaction, but does not touch the version. So after a commit the cached copy
  still matches the version, and the next `ConcurrentReadTx` lays the pre-commit buffer over the
  post-commit bbolt transaction. The third reproduction above, step by step:

  1. A batch transaction puts `k1` into the `Key` bucket and unlocks. The write-back copies
     `k1` into the read buffer and increments `bufVersion` to `v`.
  2. A `ConcurrentReadTx` copies the read buffer (with `k1`) into the cache, at version `v`.
  3. `ForceCommit` commits `k1` into bbolt and calls `readTx.reset`: the read buffer is empty,
     its version is still `v`.
  4. The next `ConcurrentReadTx` finds the cache at version `v`, equal to the buffer's, and
     reuses the copy with `k1`, over a bbolt transaction that also has `k1`.
  5. `UnsafeRange(Key, "k0", "k9")` returns bbolt's entries followed by the buffer's: `k1`
     twice.

  In the first reproduction the same stale copy is cached between the two critical sections of
  `Unlock`: the write-back releases `readTx`, a reader caches the buffer with `k`, and the
  commit that follows (forced by the pending delete) removes `k` from bbolt and resets the
  buffer, version unchanged.

  ```go
  // server/storage/backend/backend.go:321-327 and 356-359 (etcd main f061acd09)
  	curCache := b.txReadBufferCache.buf
  	curCacheVer := b.txReadBufferCache.bufVersion
  	curBufVer := b.readTx.buf.bufVersion

  	isEmptyCache := curCache == nil
  	isStaleCache := curCacheVer != curBufVer // <-

  	// ...
  	if isEmptyCache || curCacheVer == b.txReadBufferCache.bufVersion {
  		// continue if the cache is never set or no one has modified the cache
  		b.txReadBufferCache.buf = buf
  		b.txReadBufferCache.bufVersion = curBufVer
  ```

  ```go
  // server/storage/backend/batch_tx.go:381-398 and read_tx.go:133-138 (etcd main f061acd09)
  func (t *batchTxBuffered) unsafeCommit(stop bool) {
  	// ...
  	if t.backend.readTx.tx != nil {
  		// ...
  		t.backend.readTx.reset() // <-
  	}
  // read_tx.go
  func (rt *readTx) reset() {
  	rt.buf.reset() // <- the buffer is emptied, bufVersion is not changed
  	rt.buckets = make(map[BucketID]*bolt.Bucket)
  	rt.tx = nil
  	rt.txWg = new(sync.WaitGroup)
  }
  ```

  ```go
  // server/storage/backend/batch_tx.go:328-334 and 355-357 (etcd main f061acd09)
  func (t *batchTxBuffered) Unlock() {
  	if t.pending != 0 {
  		t.backend.readTx.Lock() // blocks txReadBuffer for writing.
  		// gofail: var beforeWritebackBuf struct{}
  		t.buf.writeback(&t.backend.readTx.buf)
  		// gofail: var afterWritebackBuf struct{}
  		t.backend.readTx.Unlock() // <- a reader can cache the buffer here
  		// ...
  		if t.pending >= t.backend.batchLimit || t.pendingDeleteOperations > 0 {
  			t.commit(false) // <-
  		}
  ```
- **Expected**: a `ConcurrentReadTx` sees the batch transaction's committed and written-back
  state at some instant: after a commit, not the read buffer of before it.
- **How the proof handles it**: the backend's contract makes the writer's `Unlock` take the
  readers' whole view of the backend (`notes/decisions.md`, "The backend: the locks and the
  views"): a reader needs a fraction of that view, so no reader runs during an `Unlock`, as
  mvcc's `s.revMu` ensures for the store's readers; and the cache's invariant says only that a
  cached copy at the buffer's version, over the current bbolt snapshot, reads as the buffer does
  on the buckets the hook leaves alone (the hook's buckets are excluded from what
  `ConcurrentReadTx` promises).
- **Possible fixes**: increment `bufVersion` in `readTx.reset` (or in `unsafeCommit`), so a
  commit invalidates the cache; or do the write-back and the commit in one `readTx.Lock`
  critical section.
- **Found**: 2026-10-12, designing the backend's read-side invariant for its proof (the cache's
  invariant failed across `Unlock`).
