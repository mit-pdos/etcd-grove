package bbolt

import (
	"bytes"
	"errors"
	"fmt"
	"path/filepath"
	"testing"
)

// A Commit whose meta page reaches the file but whose write then reports an error rolls back
// over a database whose newest valid meta is the new one: the pages the transaction freed
// become free while an open reader still reads them.
func TestReproMetaWriteFailFreesReaderPages(t *testing.T) { reproMetaFail(t, true) }

// The control: without the injected error, the reader's snapshot is kept.
func TestReproMetaWriteFailControl(t *testing.T) { reproMetaFail(t, false) }

func reproMetaFail(t *testing.T, inject bool) {
	// A large initial mapping: no remap (which would wait for the open reader).
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, &Options{InitialMmapSize: 64 << 20})
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()

	old := bytes.Repeat([]byte("o"), 100)
	if err := db.Update(func(tx *Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		for i := 0; i < 200; i++ {
			if err := b.Put([]byte(fmt.Sprintf("k%04d", i)), old); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}

	// A reader that stays open, holding a value in the mapping.
	rtx, err := db.Begin(false)
	if err != nil {
		t.Fatal(err)
	}
	defer rtx.Rollback()
	seen := rtx.Bucket([]byte("b")).Get([]byte("k0100"))
	if !bytes.Equal(seen, old) {
		t.Fatal("unexpected initial value")
	}

	// A writer rewrites every key (all its leaves are freed); the meta page's write lands in
	// the file, then reports an error (a short write after the meta's bytes, or an fdatasync
	// failure: this test fakes the write's error).
	realWriteAt := db.ops.writeAt
	db.ops.writeAt = func(b []byte, off int64) (int, error) {
		n, err := realWriteAt(b, off)
		if inject && err == nil && off < int64(2*db.pageSize) {
			return n, errors.New("injected error after the meta page was written")
		}
		return n, err
	}
	err = db.Update(func(tx *Tx) error {
		b := tx.Bucket([]byte("b"))
		for i := 0; i < 200; i++ {
			if err := b.Put([]byte(fmt.Sprintf("k%04d", i)), bytes.Repeat([]byte("n"), 100)); err != nil {
				return err
			}
		}
		return nil
	})
	db.ops.writeAt = realWriteAt
	if inject && err == nil {
		t.Fatal("expected the injected error")
	}
	if !inject && err != nil {
		t.Fatal(err)
	}
	t.Logf("commit returned: %v", err)
	if err := db.View(func(tx *Tx) error {
		t.Logf("a new reader after it sees k0100 = %q...", tx.Bucket([]byte("b")).Get([]byte("k0100"))[:10])
		return nil
	}); err != nil {
		t.Fatal(err)
	}

	// Writers reuse the free pages.
	for round := 0; round < 5; round++ {
		if err := db.Update(func(tx *Tx) error {
			b := tx.Bucket([]byte("b"))
			for i := 0; i < 200; i++ {
				if err := b.Put([]byte(fmt.Sprintf("k%04d", i)), bytes.Repeat([]byte{byte('a' + round)}, 100)); err != nil {
					return err
				}
			}
			return nil
		}); err != nil {
			t.Fatal(err)
		}
	}

	// The open reader's snapshot must still show the old value.
	now := rtx.Bucket([]byte("b")).Get([]byte("k0100"))
	if !bytes.Equal(now, old) || !bytes.Equal(seen, old) {
		t.Fatalf("the open reader's snapshot changed under it: Get now %q..., the value read before now %q...",
			now[:min(len(now), 10)], seen[:min(len(seen), 10)])
	}
}
