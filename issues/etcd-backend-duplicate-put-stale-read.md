# The read buffer keeps both puts of one key: `ReadTx` returns the older value

- **Status**: open (not filed). An unstated precondition of `BatchTx.UnsafePut`; no etcd
  caller is known to break it.
- **Where**: `server/storage/backend/tx_buffer.go` at the etcd pin of `etc/goose.py`
  (`bc8b52a50`): `txWriteBuffer.writeback` (`sort.Sort(wb)` under "assume no duplicate keys"),
  `bucketBuffer.merge` (it returns without `dedupe` when the read buffer's entry was empty,
  `bb.used == bbsrc.used`, or when the old entries are all below the new ones),
  `bucketBuffer.Range` (it answers a single key with the *first* entry not below it). The API
  (`UnsafeWriter.UnsafePut` in `batch_tx.go`) says only "must be called holding the lock".
- **What happens**: two `UnsafePut`s of the same key in one batch-lock session (between two
  `Unlock`s), into a non-sequential bucket whose read-buffer entry survived the last commit
  (the bucket was written back before it: `txBuffer.reset` keeps an entry that was used, with
  `used = 0`), are written back by `Unlock` as two entries: `writeback` takes the existing
  entry's branch, sorts the write buffer (`sort.Sort`, not stable beyond 12 entries, so either
  order), and `merge` appends without deduplicating. `ReadTx`/`ConcurrentReadTx`'s
  `UnsafeRange` then returns the first entry, the older value (with fewer than 13 entries
  `sort.Sort` happens to be stable), while bbolt, and so `BatchTx`'s `UnsafeRange`, has the
  newer one. Until the next commit resets the read buffer, the two transactions disagree.
  (`UnsafeForEach` visits both, newest last, so `VerifyBackendConsistency`, which builds maps,
  does not see it.)

  Reproduction (`server/storage/backend/stale_read_test.go`, fails at the pin with
  `ReadTx reads "v2", BatchTx reads "v3"`):

  ```go
  package backend_test

  import (
  	"testing"
  	"time"

  	"go.etcd.io/etcd/server/v3/storage/backend"
  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  	"go.etcd.io/etcd/server/v3/storage/schema"
  )

  func readBoth(t *testing.T, b backend.Backend, key []byte) (string, string) {
  	rtx := b.ReadTx()
  	rtx.RLock()
  	_, rv := rtx.UnsafeRange(schema.Test, key, nil, 0)
  	rtx.RUnlock()
  	tx := b.BatchTx()
  	tx.Lock()
  	_, wv := tx.UnsafeRange(schema.Test, key, nil, 0)
  	tx.Unlock()
  	if len(rv) != 1 || len(wv) != 1 {
  		t.Fatalf("missing key: read %q, batch %q", rv, wv)
  	}
  	return string(rv[0]), string(wv[0])
  }

  func TestReadTxStaleAfterDuplicatePut(t *testing.T) {
  	b, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
  	defer betesting.Close(t, b)

  	tx := b.BatchTx()
  	tx.Lock()
  	tx.UnsafeCreateBucket(schema.Test)
  	tx.UnsafePut(schema.Test, []byte("foo"), []byte("v1"))
  	tx.Unlock()
  	tx.Commit()

  	tx.Lock()
  	tx.UnsafePut(schema.Test, []byte("foo"), []byte("v2"))
  	tx.UnsafePut(schema.Test, []byte("foo"), []byte("v3"))
  	tx.Unlock()

  	r, w := readBoth(t, b, []byte("foo"))
  	if r != w {
  		t.Errorf("ReadTx reads %q, BatchTx reads %q", r, w)
  	}
  }
  ```

  The pre-commit hook (`cindex`'s `UnsafeSave`, which puts the same two meta keys at every
  commit, even a `ForceCommit` with nothing pending) does not reach it: its puts stay in the
  write buffer across commits, but the second commit's `reset` drops the read buffer's emptied
  entry, so the next write-back takes `writeback`'s other branch, which deduplicates.
- **Expected**: the read transactions see the batch transaction's last write of a key (the
  write buffer's "pending updates", `txWriteBuffer`'s comment), or the API states that a key
  is put at most once per lock session.
- **How the proof handles it**: the write buffer's specs (`Spec/go_etcd_io/etcd/server/v3/
  storage/backend/txWriteBuffer__writeback.lean`) take the premise that a non-sequential
  bucket's buffered puts have distinct keys (a sequential bucket's are increasing, which
  `putSeq`'s `verify` check states); the batch transaction's `UnsafePut` carries it as a
  premise on the session's puts. Since 2026-10-13 (unit 7) the premise is what the code needs:
  a duplicate is allowed in a bucket the read buffer lacks (`writeback`'s `!ok` branch
  deduplicates it, `WBuf.WfR`) or, in the pre-commit hook's window, one whose read-buffer
  bucket is empty (the commit's `reset` that follows drops it: `wbDupOk`). With it the
  consistent-index hook's re-puts at every commit are proved harmless
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/CindexBackend.lean`); a client's duplicate put
  into a bucket the read buffer has is still excluded, as the reproduction shows it must be.
- **Possible fixes**: in `writeback`, deduplicate a non-sequential bucket's buffer on both
  branches (`wb.dedupe()` in place of `sort.Sort(wb)`; `dedupe` sorts stably and keeps the
  newest); or make `merge` deduplicate whenever the source is not known to be duplicate-free.
- **Found**: 2026-10-12, specifying `tx_buffer.go` for the backend's proof (the write-back's
  postcondition needed the premise).
