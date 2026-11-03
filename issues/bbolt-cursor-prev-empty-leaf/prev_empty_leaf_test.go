package bbolt_test

import (
	"fmt"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
)

func key(i int) []byte { return []byte(fmt.Sprintf("k%05d", i)) }

// In a write transaction, delete a run of keys covering whole leaves, then Prev from the
// first key after the run.
func TestPrevOverEmptyLeaf(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	val := make([]byte, 100)
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		for i := 0; i < 2000; i++ {
			if err := b.Put(key(i), val); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	tx, err := db.Begin(true)
	if err != nil {
		t.Fatal(err)
	}
	defer tx.Rollback()
	b := tx.Bucket([]byte("b"))
	for i := 500; i < 1500; i++ {
		if err := b.Delete(key(i)); err != nil {
			t.Fatal(err)
		}
	}
	c := b.Cursor()
	k, _ := c.Seek(key(1500))
	if string(k) != string(key(1500)) {
		t.Fatalf("seek: %q", k)
	}
	k, _ = c.Prev()
	t.Logf("Prev after Seek(k01500): %q (expected %q)", k, key(499))
	if string(k) != string(key(499)) {
		t.Errorf("Prev returned %q, want %q", k, key(499))
	}
	c2 := b.Cursor()
	n := 0
	for k, _ := c2.Last(); k != nil; k, _ = c2.Prev() {
		n++
	}
	t.Logf("backward walk saw %d keys, want 1000", n)
	if n != 1000 {
		t.Errorf("backward walk saw %d keys", n)
	}
	for i := 1500; i < 2000; i++ {
		_ = b.Delete(key(i))
	}
	c3 := b.Cursor()
	k, _ = c3.Last()
	t.Logf("Last after deleting the tail: %q, want %q", k, key(499))
	if string(k) != string(key(499)) {
		t.Errorf("Last returned %q", k)
	}
}
