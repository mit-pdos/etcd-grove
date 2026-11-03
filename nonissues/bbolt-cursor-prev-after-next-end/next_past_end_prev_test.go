package bbolt_test

import (
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
)

// Cursor.Prev after the end: Seek past the end then Prev gives the last key; Last, Next (nil),
// then Prev gives the second to last.
func TestNextPastEndThenPrev(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	_ = db.Update(func(tx *bolt.Tx) error {
		b, _ := tx.CreateBucket([]byte("b"))
		for _, k := range []string{"a", "b", "c"} {
			_ = b.Put([]byte(k), []byte(k))
		}
		return nil
	})
	_ = db.View(func(tx *bolt.Tx) error {
		c := tx.Bucket([]byte("b")).Cursor()
		c.Seek([]byte("z"))
		k1, _ := c.Prev()
		c.Last()
		kn, _ := c.Next()
		k2, _ := c.Prev()
		t.Logf("Seek past end, Prev: %q; Last, Next: %q, Prev: %q", k1, kn, k2)
		if string(k1) != string(k2) {
			t.Errorf("Prev after the end differs: %q after Seek past the end, %q after Next past the end", k1, k2)
		}
		return nil
	})
}
