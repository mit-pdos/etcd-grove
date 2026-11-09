package bbolt

import (
	"bytes"
	"errors"

	bolt "go.etcd.io/bbolt"
	bolterrors "go.etcd.io/bbolt/errors"
)

// REQ bbolt/nested: nested buckets with sequence counters: a child bucket's keys are its own; a
// bucket's key reads as nil from Get and as a nil value from cursors and ForEach; NextSequence
// counts up; deleting the parent deletes the child and stales its handle's use (here: a fresh
// lookup finds nothing); Last and Prev walk backwards in a read transaction.
// Users: bbolt's documented API (no etcd user; the general client the spec serves).
// Assumes: db open, its close right held; bucket "p" absent at the start.
// Specs: DB.Update.spec, DB.View.spec, Tx.CreateBucket.spec, Bucket.CreateBucket.spec,
// Bucket.CreateBucketIfNotExists.spec, Bucket.Bucket.spec, Bucket.Put.spec, Bucket.Get.spec,
// Bucket.NextSequence.spec, Bucket.Sequence.spec, Bucket.ForEach.spec,
// Bucket.ForEachBucket.spec, Bucket.DeleteBucket.spec, Tx.DeleteBucket.spec, Tx.ForEach.spec,
// Cursor.Last.spec, Cursor.Prev.spec; laws: bktH_live.
func ReqNested(db *bolt.DB) {
	err := db.Update(func(tx *bolt.Tx) error {
		p, err := tx.CreateBucket([]byte("p"))
		if err != nil {
			return err
		}
		c, err := p.CreateBucket([]byte("c"))
		if err != nil {
			panic("nested: create child failed")
		}
		if _, err := p.CreateBucket([]byte("c")); !errors.Is(err, bolterrors.ErrBucketExists) {
			panic("nested: duplicate bucket created")
		}
		if err := c.Put([]byte("k"), []byte("v")); err != nil {
			panic("nested: put failed")
		}
		if err := p.Put([]byte("c"), []byte("x")); !errors.Is(err, bolterrors.ErrIncompatibleValue) {
			panic("nested: a value over a bucket")
		}
		if p.Get([]byte("k")) != nil || p.Get([]byte("c")) != nil {
			panic("nested: the parent sees the child's key, or a bucket as a value")
		}
		n1, err := c.NextSequence()
		if err != nil {
			panic("nested: sequence failed")
		}
		n2, _ := c.NextSequence()
		if n2 != n1+1 || c.Sequence() != n2 {
			panic("nested: sequence does not count")
		}
		seen := 0
		_ = p.ForEach(func(k, v []byte) error {
			if !bytes.Equal(k, []byte("c")) || v != nil {
				panic("nested: ForEach shows a bucket as a value")
			}
			seen++
			return nil
		})
		_ = p.ForEachBucket(func(k []byte) error { seen++; return nil })
		if seen != 2 {
			panic("nested: ForEach missed the child")
		}
		if c2, err := p.CreateBucketIfNotExists([]byte("c")); err != nil || c2.Get([]byte("k")) == nil {
			panic("nested: CreateBucketIfNotExists lost the child")
		}
		return nil
	})
	if err != nil {
		return
	}
	_ = db.View(func(tx *bolt.Tx) error {
		p := tx.Bucket([]byte("p"))
		if p == nil {
			panic("nested: committed bucket missing")
		}
		c := p.Bucket([]byte("c"))
		if c == nil || !bytes.Equal(c.Get([]byte("k")), []byte("v")) {
			panic("nested: committed child missing")
		}
		cur := p.Cursor()
		if k, _ := cur.Last(); !bytes.Equal(k, []byte("c")) {
			panic("nested: Last")
		}
		if k, _ := cur.Prev(); k != nil {
			panic("nested: Prev before the first")
		}
		names := 0
		_ = tx.ForEach(func(name []byte, b *bolt.Bucket) error {
			if b == nil {
				panic("nested: a top-level key is not a bucket")
			}
			names++
			return nil
		})
		if names == 0 {
			panic("nested: Tx.ForEach missed p")
		}
		return nil
	})
	_ = db.Update(func(tx *bolt.Tx) error {
		if err := tx.DeleteBucket([]byte("p")); err != nil {
			panic("nested: delete parent failed")
		}
		if tx.Bucket([]byte("p")) != nil {
			panic("nested: deleted bucket still there")
		}
		return nil
	})
}

// REQ bbolt/read-only-put: a mutation on a read transaction fails with ErrTxNotWritable and
// changes nothing; Commit of a read transaction fails and leaves it live.
// Users: bbolt's documented API (etcd never mutates in a read transaction).
// Assumes: db open; the bucket "p" exists in the committed data; the caller's thread token.
// Specs: DB.Begin.spec, Tx.Bucket.spec, Bucket.Put.spec, Bucket.Delete.spec,
// Bucket.NextSequence.spec, Tx.Commit.spec, Tx.Rollback.spec.
func ReqReadOnlyPut(db *bolt.DB) {
	tx, err := db.Begin(false)
	if err != nil {
		return
	}
	b := tx.Bucket([]byte("p"))
	if b == nil {
		panic("read-only: bucket missing")
	}
	if err := b.Put([]byte("k"), []byte("v")); !errors.Is(err, bolterrors.ErrTxNotWritable) {
		panic("read-only: put allowed")
	}
	if err := b.Delete([]byte("k")); !errors.Is(err, bolterrors.ErrTxNotWritable) {
		panic("read-only: delete allowed")
	}
	if _, err := b.NextSequence(); err == nil {
		panic("read-only: sequence allowed")
	}
	if err := tx.Commit(); !errors.Is(err, bolterrors.ErrTxNotWritable) {
		panic("read-only: commit allowed")
	}
	if err := tx.Rollback(); err != nil {
		panic("read-only: rollback after a failed commit")
	}
}

// REQ bbolt/cursor-delete: deleting while iterating: Delete at the cursor, then reposition by Seek
// (Go: "reposition your cursor after mutating data"); every key is gone at the end.
// Users: bbolt's documented API (no etcd user).
// Assumes: tx a write transaction; b a current handle of a bucket holding no nested bucket.
// Specs: Bucket.Cursor.spec, Cursor.First.spec, Cursor.Delete.spec, Cursor.Seek.spec,
// Bucket.Get.spec; laws: txBytes_acc.
func ReqCursorDelete(b *bolt.Bucket) {
	c := b.Cursor()
	for k, _ := c.First(); k != nil; k, _ = c.Seek(k) {
		k = append([]byte(nil), k...)
		if err := c.Delete(); err != nil {
			panic("cursor delete: failed")
		}
		if b.Get(k) != nil {
			panic("cursor delete: key still there")
		}
	}
	if k, _ := c.First(); k != nil {
		panic("cursor delete: a key left")
	}
}
