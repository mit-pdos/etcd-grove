package bbolt_test

import (
	"fmt"
	"path/filepath"
	"testing"
	"time"

	bolt "go.etcd.io/bbolt"
)

func lastKey(i int) []byte { return []byte(fmt.Sprintf("k%05d", i)) }

// In a write transaction, delete every key of a multi-leaf bucket, then Last().
func TestLastAllDeleted(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	val := make([]byte, 100)
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		for i := 0; i < 2000; i++ {
			if err := b.Put(lastKey(i), val); err != nil {
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
	b := tx.Bucket([]byte("b"))
	for i := 0; i < 2000; i++ {
		if err := b.Delete(lastKey(i)); err != nil {
			t.Fatal(err)
		}
	}
	done := make(chan []byte)
	go func() {
		c := b.Cursor()
		k, _ := c.Last()
		done <- k
	}()
	select {
	case k := <-done:
		t.Logf("Last returned %q", k)
	case <-time.After(5 * time.Second):
		t.Fatalf("Last did not return within 5s (all leaves empty in a write tx)")
	}
}
