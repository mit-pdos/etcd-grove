package bbolt

import (
	"bytes"
	"path/filepath"
	"testing"
)

// A bucket handle used in its own transaction after the bucket is deleted and re-created: Put
// through it panics ("assertion failed: nodes map expected") when the bucket was used before
// the delete. Found by etc/spec-test/bbolt (seed 139 of its run).
func TestReproDeletedBucketHandlePutPanics(t *testing.T) {
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	tx, err := db.Begin(true)
	if err != nil {
		t.Fatal(err)
	}
	defer tx.Rollback()
	old, err := tx.CreateBucketIfNotExists([]byte("a"))
	if err != nil {
		t.Fatal(err)
	}
	if err := tx.DeleteBucket([]byte("a")); err != nil {
		t.Fatal(err)
	}
	if _, err := tx.CreateBucketIfNotExists([]byte("a")); err != nil {
		t.Fatal(err)
	}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("Put through the old handle panicked: %v", r)
		}
	}()
	err = old.Put([]byte("k"), []byte("v"))
	t.Logf("Put through the old handle returned %v", err)
}

// Reads and deletes through the old handle do not panic: they return nil and see nothing of the
// re-created bucket (here: its key k2), with no error.
func TestReproDeletedBucketHandleSilent(t *testing.T) {
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	tx, err := db.Begin(true)
	if err != nil {
		t.Fatal(err)
	}
	defer tx.Rollback()
	old, err := tx.CreateBucketIfNotExists([]byte("a"))
	if err != nil {
		t.Fatal(err)
	}
	if err := old.Put([]byte("k1"), []byte("v1")); err != nil {
		t.Fatal(err)
	}
	if err := tx.DeleteBucket([]byte("a")); err != nil {
		t.Fatal(err)
	}
	cur, err := tx.CreateBucketIfNotExists([]byte("a"))
	if err != nil {
		t.Fatal(err)
	}
	if err := cur.Put([]byte("k2"), []byte("v2")); err != nil {
		t.Fatal(err)
	}
	if err := old.Delete([]byte("k2")); err != nil {
		t.Fatalf("Delete through the old handle: %v", err)
	}
	if v := cur.Get([]byte("k2")); !bytes.Equal(v, []byte("v2")) {
		t.Fatalf("k2 = %q after the old handle's Delete", v)
	}
	if k, _ := old.Cursor().Seek([]byte("k2")); !bytes.Equal(k, []byte("k2")) {
		t.Errorf("bucket a holds k2, but the old handle's cursor Seek(k2) returns %q, and its Delete(k2) returned nil and left k2", k)
	}
}
