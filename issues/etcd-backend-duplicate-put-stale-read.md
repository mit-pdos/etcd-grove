---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#21986 issue open: same bug (merge's no-overlap fast path skips dedupe; a single-key read returns the older value)
  - etcd-io/etcd#21987 pr open: fix for #21986 (dedupe intra-batch duplicates in writeback before merge)
  - etcd-io/etcd#22298 pr open: same fix (dedupe on every writeback path into an existing read bucket), filed as hardening without an issue
  - etcd-io/etcd#21985 pr closed: earlier fix attempt for the same bug (dedupe on the merge path), superseded by #21987
---

# The read buffer keeps both puts of one key: `ReadTx` returns the older value

- **Status**: fixed in the fork (2026-10-18, D19i (A)): etcd-io/etcd#21987 (the fix for #21986:
  `writeback` calls `wb.dedupe()` for a non-sequential bucket on both branches) cherry-picked onto
  `goose-lean` as `ea78ec948` (author Frans Kaashoek, co-authored by the PR's author), with the two
  reproductions below as regression tests (both fail without the fix; `go test ./server/storage/...`
  passes). Chosen over #22298 (the same one-line code change, plus a comment and a test): #21987 is
  the smaller diff and the fix of the filed issue. It is the pin of `etc/goose.py`'s project `etcd`
  (and then `06aa6e6e`, D19i part 1's `raftAdvancedC` fix on top of it); **to be pushed to
  `upamanyus/etcd` by the user**. The backend's specs no longer exclude a repeated put
  (`UnsafePut`'s premise and `wbDupOk` gone; `txWriteBuffer.writeback` proved for the fixed code).
  Upstream: both PRs still open. Until the fix: an unstated precondition of `BatchTx.UnsafePut`,
  and one etcd caller known to break it, the storage-version migration
  (`EtcdServer.monitorStorageVersion`), below, "An etcd caller".
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
- **How the proof handles it** (until 2026-10-18; since then the fork's fix, above, and no
  premise): the write buffer's specs (`Spec/go_etcd_io/etcd/server/v3/
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
- **An etcd caller** (2026-10-18, audit B2, `notes/decisions.md` D19i): the storage-version
  monitor (`server.go`'s `monitorStorageVersion`, `version/monitor.go`'s
  `UpdateStorageVersionIfNeeded`, `adapters.go`'s `UpdateStorageVersion`) migrates the
  backend under one `LockOutsideApply` session with `schema.UnsafeMigrate`. From v3.5 (no
  `storageVersion` key, a non-zero term: `UnsafeDetectSchemaVersion`) to v3.7 the plan has two
  steps, and the session puts `meta/storageVersion` three times: `""` (the v3.6 step's
  `addNewField`, a `setKeyAction`), `"3.6.0"` and `"3.7.0"` (`UnsafeSetStorageVersion` after
  each step, `migration.go:101`). `meta` is not sequential, and its read-buffer entry is
  present and empty after a commit that follows a write-back into it (as in the reproduction;
  in a running server the consistent index's and term's puts write into it, so whether the
  monitor's session meets that state depends on when the backend commits). Then `Unlock`'s
  write-back keeps all three, and a `ReadTx` reads
  `""`: `EtcdServer.StorageVersion()` (`schema.DetectSchemaVersion` over `s.be.ReadTx()`) fails
  to parse it and falls back to the term, answering 3.5.0 until the next commit (at most the
  batch interval, 100 ms by default), while the batch transaction reads 3.7.0. The monitor's
  next round then migrates again (a no-op plan), and a `Status` call in that window reports the
  old storage version. It can happen on every new cluster: the monitor migrates once the
  cluster version is set (the putget example reaches the migration). Reproduction at the pin (both revisions of
  the fork agree on `server/storage` and the monitor), `server/storage/schema/
  migrate_stale_read_test.go`, which fails with `ReadTx: 3.5.0 (err <nil>); BatchTx: 3.7.0`:

  ```go
  package schema

  import (
  	"testing"
  	"time"

  	"go.uber.org/zap/zaptest"

  	"go.etcd.io/etcd/api/v3/version"
  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  )

  func TestMigrateStaleRead(t *testing.T) {
  	lg := zaptest.NewLogger(t)
  	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
  	defer betesting.Close(t, be)

  	tx := be.BatchTx()
  	tx.LockOutsideApply()
  	UnsafeCreateMetaBucket(tx)
  	UnsafeUpdateConsistentIndex(tx, 1, 1)
  	tx.Unlock()
  	be.ForceCommit()

  	tx.LockOutsideApply()
  	if err := UnsafeMigrate(lg, tx, nil, version.V3_7); err != nil {
  		t.Fatal(err)
  	}
  	tx.Unlock()

  	rv, rerr := DetectSchemaVersion(lg, be.ReadTx())
  	tx.LockOutsideApply()
  	bv := UnsafeReadStorageVersion(tx)
  	tx.Unlock()
  	if rerr != nil || bv == nil || rv.String() != bv.String() {
  		t.Fatalf("ReadTx: %v (err %v); BatchTx: %v", rv, rerr, bv)
  	}
  }
  ```

  Either fix below repairs it, as would `UnsafeMigrate` putting the key once per session.
- **Possible fixes**: in `writeback`, deduplicate a non-sequential bucket's buffer on both
  branches (`wb.dedupe()` in place of `sort.Sort(wb)`; `dedupe` sorts stably and keeps the
  newest); or make `merge` deduplicate whenever the source is not known to be duplicate-free.
- **Found**: 2026-10-12, specifying `tx_buffer.go` for the backend's proof (the write-back's
  postcondition needed the premise).
