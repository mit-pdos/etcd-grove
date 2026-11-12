// Package bbolt holds the requirement snippets of bbolt's public API (batch 4c): how etcd's
// backend (server/storage/backend), this repository's bank test (examples/bbolt/bank) and the
// other users call it, each aspect they rely on a panic on its violation.
package bbolt

import (
	"bytes"
	"errors"
	"io"
	"os"
	"syscall"

	bolt "go.etcd.io/bbolt"
	bolterrors "go.etcd.io/bbolt/errors"
)

var keyBucket = []byte("key")

// REQ bbolt/backend-open: etcd's options open the file; a failure is fatal for etcd.
// Users: server/storage/backend/backend.go:216-237 (newBackend: `&bolt.Options{}`, then
// `*bopts = *boltOpenOptions`, whose keyed literal is an untranslated package initializer, the
// backend's assumed fact; then field stores).
// Assumes: path is the database's closed file (boltFile, boltClosed: from fileHolds_alloc of a
// file that exists, or boltFresh_alloc of etcd's first boot); a pointer-typed logger meeting
// boltLogger (here nil); with noSync false, the caller supplies Open's sync update (it holds
// boltState γ 1 σ: boltState_settle_au; Open fdatasyncs the file before any commit).
// Specs: optsLit.spec, optsAlloc.spec, Open.spec; laws: optsAt_int, optsAt_bool, fileHolds_alloc,
// boltFresh_alloc, boltState_settle_au.
func ReqBackendOpen(path string, noSync bool) *bolt.DB {
	opts := &bolt.Options{}
	opts.MmapFlags = syscall.MAP_POPULATE
	opts.NoFreelistSync = true
	opts.NoSync = noSync
	opts.NoGrowSync = noSync
	db, err := bolt.Open(path, 0o600, opts)
	if err != nil {
		return nil // the backend logs and panics: an environment failure
	}
	return db
}

// REQ bbolt/backend-batch: the batch write transaction: create the bucket, put (with a
// FillPercent for sequential keys), delete, range by Seek/Next, commit, then read the
// transaction's statistics; every bbolt error here is fatal for etcd, so none may occur but a
// commit's (an environment failure). The range sees the batch's own writes, in key order.
// Users: server/storage/backend/batch_tx.go:136-246 (UnsafeCreateBucket, unsafePut,
// UnsafeRange, unsafeRange, UnsafeDelete), :280-305 (commit), backend.go:1101 (unsafeBegin).
// Assumes: db open; the root has no plain value at keyBucket (no Tx method puts one there);
// keyBucket holds no nested bucket; k1 < k2 (bytes.Compare), both non-empty and
// within MaxKeySize; the caller holds boltState γ 1 σ (the backend's batch lock), from which it
// builds Commit's updates (boltState_commit_au: both, the settling one given by the commit's).
// Specs: DB.Begin.spec (write), DB.Stats.spec (the write transaction pays: statSlot_wtx),
// Tx.CreateBucketIfNotExists.spec, Tx.Bucket.spec, Bucket.Put.spec, Bucket.Delete.spec,
// Bucket.Cursor.spec, Cursor.Seek.spec, Cursor.Next.spec, Tx.Commit.spec, Tx.Stats.spec; laws:
// boltTx_fill, bktH_live, bktOwn_bktH (Begin's token of keyBucket, or CreateBucketIfNotExists'
// for a new one, which Tx.Bucket returns at the cached handle), txBytes_acc, boltTx_wf (the order),
// Ent.atPath_modAt, Ent.curEnts_put, Ent.curEnts_del (the range after the put and the delete),
// statSlot_wtx, boltState_commit_au, putLoan_done.
func ReqBackendBatch(db *bolt.DB, k1, k2 []byte) {
	tx, err := db.Begin(true)
	if err != nil {
		return // the database was closed
	}
	_ = db.Stats().FreePageN // backend.begin(true)'s metrics, holding only the write transaction
	if _, err := tx.CreateBucketIfNotExists(keyBucket); err != nil {
		panic("batch: create bucket failed")
	}
	b := tx.Bucket(keyBucket)
	if b == nil {
		panic("batch: bucket missing after create")
	}
	b.FillPercent = 0.9
	if err := b.Put(k1, []byte("v1")); err != nil {
		panic("batch: put failed")
	}
	if err := b.Put(k2, []byte("v2")); err != nil {
		panic("batch: put failed")
	}
	if err := b.Delete(k1); err != nil {
		panic("batch: delete failed")
	}
	c := b.Cursor()
	var keys [][]byte
	for k, _ := c.Seek(k1); k != nil; k, _ = c.Next() {
		keys = append(keys, k)
	}
	found := false
	for _, k := range keys {
		if bytes.Equal(k, k1) {
			panic("batch: range shows a deleted key")
		}
		if bytes.Equal(k, k2) {
			found = true
		}
	}
	if !found {
		panic("batch: range misses a key written in the batch")
	}
	for i := 1; i < len(keys); i++ {
		if bytes.Compare(keys[i-1], keys[i]) >= 0 {
			panic("batch: range out of order")
		}
	}
	if v := b.Get(k2); !bytes.Equal(v, []byte("v2")) {
		panic("batch: lost write")
	}
	err = tx.Commit()
	_ = tx.Stats().RebalanceTime // read after the commit
	if err != nil {
		return // fatal in etcd: an environment failure
	}
}

// REQ bbolt/backend-read: the shared read transaction: a snapshot that later commits do not
// change, read concurrently through per-goroutine cursors; its size and the database's page size
// for the metrics; rolled back on its own goroutine.
// Users: server/storage/backend/read_tx.go:95-120 (UnsafeRange), backend.go:598-606
// (finishDefrag's size), batch_tx.go:385-400 (the old read transaction's rollback).
// Assumes: db open; the caller's thread token (and the writer goroutine's); k non-empty, within
// MaxKeySize and with len(k)+5 within bboltEntryMax (the writer's Put); the client keeps
// boltState in an invariant (the writer's updates, commitAU, come from it); fractions of the read
// transaction are lent to the reader goroutines (boltTx_frac).
// Specs: DB.Begin.spec (read), DB.Update.spec, Tx.Bucket.spec, Bucket.Get.spec, Tx.Size.spec, Tx.DB.spec,
// DB.Stats.spec (statSlot of the transaction), DB.Info.spec, Tx.Rollback.spec.
func ReqBackendRead(db *bolt.DB, k []byte) {
	tx, err := db.Begin(false)
	if err != nil {
		return
	}
	var before []byte
	if b := tx.Bucket(keyBucket); b != nil {
		before = append([]byte(nil), b.Get(k)...)
	}
	go func() { // a concurrent writer (not waited for: its commit may need to remap, which waits
		// for this reader)
		_ = db.Update(func(wtx *bolt.Tx) error {
			b, err := wtx.CreateBucketIfNotExists(keyBucket)
			if err != nil {
				return err
			}
			return b.Put(k, []byte("other"))
		})
	}()
	if b := tx.Bucket(keyBucket); b != nil {
		if !bytes.Equal(b.Get(k), before) {
			panic("read: the snapshot changed")
		}
	} else if before != nil {
		panic("read: the bucket vanished from the snapshot")
	}
	// the shared read transaction read by several goroutines, a cursor each, the bucket handle
	// shared (read_tx.go:95-118)
	if b := tx.Bucket(keyBucket); b != nil {
		done := make(chan struct{})
		for i := 0; i < 2; i++ {
			go func() {
				c := b.Cursor()
				for k, _ := c.First(); k != nil; k, _ = c.Next() {
				}
				done <- struct{}{}
			}()
		}
		<-done
		<-done
	}
	size := tx.Size()
	if size < 0 || size >= 1<<62 {
		panic("read: size out of range")
	}
	d := tx.DB()
	_ = size - int64(d.Stats().FreePageN)*int64(d.Info().PageSize)
	if err := tx.Rollback(); err != nil {
		panic("read: rollback failed")
	}
}

// REQ bbolt/delete-bucket-not-found: deleting a bucket that is absent returns
// ErrBucketNotFound, which the backend accepts; any other error is fatal.
// Users: server/storage/backend/batch_tx.go:147-156 (UnsafeDeleteBucket).
// Assumes: tx a write transaction, with the whole tokens of name's bucket and of the buckets below
// it (bktOwn, from Begin's for the buckets of its data: none if name is absent); the root holds
// only buckets; name non-empty.
// Specs: Tx.DeleteBucket.spec; laws: errIs_distinct, Ent.bktsUnder_mem.
func ReqDeleteBucketNotFound(tx *bolt.Tx, name []byte) {
	err := tx.DeleteBucket(name)
	if err != nil && !errors.Is(err, bolterrors.ErrBucketNotFound) {
		panic("delete bucket: unexpected error")
	}
	if tx.Bucket(name) != nil {
		panic("delete bucket: still there")
	}
}

// REQ bbolt/hash: View over the root cursor and each bucket's ForEach: every top-level key is a
// bucket; ForEach visits keys in order.
// Users: server/storage/backend/backend.go:424-455 (Hash).
// Assumes: db open; the root holds only buckets (every write goes through the backend);
// buckets hold no nested bucket.
// Specs: DB.View.spec, Tx.Cursor.spec, Cursor.First.spec, Cursor.Next.spec, Tx.Bucket.spec,
// Bucket.ForEach.spec.
func ReqHash(db *bolt.DB) {
	_ = db.View(func(tx *bolt.Tx) error {
		c := tx.Cursor()
		for next, _ := c.First(); next != nil; next, _ = c.Next() {
			b := tx.Bucket(next)
			if b == nil {
				panic("hash: a top-level key is not a bucket")
			}
			var prev []byte
			_ = b.ForEach(func(k, v []byte) error {
				if prev != nil && bytes.Compare(prev, k) >= 0 {
					panic("hash: ForEach out of order")
				}
				prev = append([]byte(nil), k...)
				return nil
			})
		}
		return nil
	})
}

// REQ bbolt/snapshot: a read transaction's WriteTo streams an image of its snapshot of Size()
// bytes, which, written to a file and synced, opens as that data.
// Users: server/storage/backend/backend.go:381-424 (Snapshot), :1129-1133 (snapshot.Close);
// etcdserver's snapshot sender and the maintenance service (through a pipe).
// Assumes: db open; w has no ReadFrom (a pipe writer); the caller's thread token.
// Specs: DB.Begin.spec (read), Tx.Size.spec, Tx.WriteTo.spec, Tx.Rollback.spec; laws:
// fileHolds_image.
func ReqSnapshot(db *bolt.DB, w io.Writer) {
	tx, err := db.Begin(false)
	if err != nil {
		return
	}
	size := tx.Size()
	n, err := tx.WriteTo(w)
	if err == nil && n != size {
		panic("snapshot: short image")
	}
	if err := tx.Rollback(); err != nil {
		panic("snapshot: rollback failed")
	}
}

// REQ bbolt/defrag: etcd's defragmentation, end to end: a temporary file the caller creates is
// opened as a second database through a custom OpenFile (one call, the one file) with NoSync; on
// Open's error the file is closed again and removed; the copy is filled from the source by
// ForEach/Put across several commits (no copy error: every key and entry read from a database is
// within Put's and CreateBucketIfNotExists' bounds); the source is closed; the copy is synced and
// closed (a failure cleans up: a second Close does nothing, the file is removed); the copy is
// renamed over the source's path and reopened there, holding what was copied.
// Users: server/storage/backend/backend.go:512-546 (createDefragTmpDB), :553-560
// (cleanupTmpDB), :565-606 (finishDefrag), :796-858 (defragdb).
// Assumes: odb open, its close right held, its boltState held whole by the caller (no other
// writer), γ.path non-empty, in the directory dir; the root of odb holds only buckets, at least
// one (an empty copy gives boltRelease no image), which hold no nested bucket; the caller allocates the copy's names at the temporary file
// (boltFresh_alloc) and holds its boltState whole (it alone writes the copy).
// Specs: os.CreateTemp, (*os.File).Name/Close, os.Remove, os.RemoveAll, os.Rename (the os
// package over OsFs: provisional, req/os.md; OsFs has no rename yet, batch-4c I7 item 6),
// Options' optsLit/optsAlloc and laws (optsAt_bool, optsAt_openFile), Open.spec (custom
// OpenFile: openFileOk one-shot, its R on an error), DB.Path.spec, DB.Begin.spec, Tx.Cursor.spec,
// Cursor.First.spec, Cursor.Next.spec, Tx.Bucket.spec, Tx.CreateBucketIfNotExists.spec,
// Bucket.ForEach.spec, Bucket.Put.spec (putLoan), Tx.Commit.spec, Tx.Rollback.spec (a finished
// transaction), DB.Begin.spec (dbBroken excluded by dbBroken_state), DB.Sync.spec,
// DB.Close.spec, DB.View.spec; laws: boltTx_wf (Ent.wf's bounds), boltState_commit_au,
// boltState_settle_au (the sync's update), putLoan_done, boltFresh_alloc, boltRelease (both
// files out of their crash invariants, the copy's bytes clean and an image of its data). The
// reopen at path has no source yet: OsFs has no rename (batch-4c I7 item 6), and neither etcd nor
// this snippet syncs the directory after it, so the renamed file's name is not durable and
// fileHolds_image (which needs it) does not apply: a crash may bring back the old file at path
// or the copy; the rename rule must say so, and bbolt then needs a generation start whose
// recoverable data is either (a recorded need: repair-bbolt.md, re-review N5).
func ReqDefrag(odb *bolt.DB, dir string) {
	path := odb.Path()
	if path == "" {
		panic("defrag: open database without a path")
	}
	tmp, err := os.CreateTemp(dir, "db.tmp.*")
	if err != nil {
		return
	}
	opts := &bolt.Options{}
	opts.NoFreelistSync = true
	opts.OpenFile = func(string, int, os.FileMode) (*os.File, error) { return tmp, nil }
	opts.Mlock = false
	opts.NoSync = true
	tdbp := tmp.Name()
	tmpdb, err := bolt.Open(tdbp, 0o600, opts)
	if err != nil {
		tmp.Close() // bbolt closed it already: an error, ignored
		_ = os.Remove(tmp.Name())
		return
	}
	cleanup := func() {
		tmpdb.Close()
		_ = os.RemoveAll(tdbp)
	}
	tx, err := odb.Begin(false)
	if err != nil {
		cleanup()
		return
	}
	tmptx, err := tmpdb.Begin(true)
	if err != nil {
		tx.Rollback()
		cleanup()
		return
	}
	copied := 0
	c := tx.Cursor()
	for next, _ := c.First(); next != nil; next, _ = c.Next() {
		b := tx.Bucket(next)
		if b == nil {
			panic("defrag: a top-level key is not a bucket")
		}
		tmpb, err := tmptx.CreateBucketIfNotExists(next)
		if err != nil {
			panic("defrag: create bucket failed")
		}
		tmpb.FillPercent = 0.9
		if err := b.ForEach(func(k, v []byte) error { return tmpb.Put(k, v) }); err != nil {
			panic("defrag: copying an entry failed")
		}
		copied++
	}
	// etcd's order (backend.go:816, 855): the copy commits while the source transaction still
	// holds the values it lent, then the source rolls back (deferred in etcd); a deferred
	// Rollback of the committed copy returns ErrTxClosed.
	err = tmptx.Commit()
	tx.Rollback()
	if tmptx.Rollback() == nil {
		panic("defrag: rollback of a committed transaction succeeded")
	}
	if err != nil {
		cleanup()
		return
	}
	// another batch on the copy: Begin(true) cannot fail on an open database whose commits all
	// succeeded (backend.go:840)
	tmptx, err = tmpdb.Begin(true)
	if err != nil {
		panic("defrag: begin after a successful commit failed")
	}
	tmptx.Rollback()
	// finishDefrag
	if err := odb.Close(); err != nil {
		cleanup()
		return // fatal in etcd
	}
	if err := tmpdb.Sync(); err != nil {
		tmpdb.Close()
		cleanup() // closes again: nothing happens
		return    // fatal in etcd
	}
	if err := tmpdb.Close(); err != nil {
		cleanup()
		return
	}
	if err := os.Rename(tdbp, path); err != nil {
		cleanup()
		return // fatal in etcd
	}
	db, err := bolt.Open(path, 0o600, nil)
	if err != nil {
		return // fatal in etcd
	}
	defer db.Close()
	found := 0
	_ = db.View(func(tx *bolt.Tx) error {
		c := tx.Cursor()
		for next, _ := c.First(); next != nil; next, _ = c.Next() {
			found++
		}
		return nil
	})
	if found != copied {
		panic("defrag: the reopened database is not the copy")
	}
}

// REQ bbolt/delete-returned: a write transaction deletes the very keys its own range returned,
// using the returned slices (not copies) as the keys: each key slice still holds its bytes after
// the deletes before it, and every deleted key is gone.
// Users: server/storage/mvcc/kvstore_compaction.go:58-71 (scheduleCompaction: UnsafeRange, then
// UnsafeDelete of each returned key), through server/storage/backend/batch_tx.go:238.
// Assumes: tx a write transaction, with keyBucket's token (bktOwn, from Begin); keyBucket holds no
// nested bucket.
// Specs: Tx.Bucket.spec, Bucket.Cursor.spec, Cursor.Seek.spec, Cursor.Next.spec,
// Bucket.Delete.spec, Bucket.Get.spec; laws: txBytes_acc (against txLive, not boltTx),
// txLive_frac.
func ReqDeleteReturned(tx *bolt.Tx, from []byte) {
	b := tx.Bucket(keyBucket)
	if b == nil {
		return
	}
	var keys [][]byte
	var saved [][]byte
	c := b.Cursor()
	for k, _ := c.Seek(from); k != nil; k, _ = c.Next() {
		keys = append(keys, k)
		saved = append(saved, append([]byte(nil), k...))
	}
	for i, k := range keys {
		if !bytes.Equal(k, saved[i]) {
			panic("delete-returned: a returned key changed under an earlier delete")
		}
		if err := b.Delete(k); err != nil {
			panic("delete-returned: delete failed")
		}
	}
	for _, k := range saved {
		if b.Get(k) != nil {
			panic("delete-returned: a deleted key is still there")
		}
	}
}
