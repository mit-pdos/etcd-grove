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
