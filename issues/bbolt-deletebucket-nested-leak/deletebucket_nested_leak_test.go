package bbolt_test

import (
	"fmt"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
)

// TestDeleteBucketNestedLeak deletes a bucket holding three non-inline nested
// buckets, in a transaction that first wrote a key into it. Afterwards no page
// may be both unreachable and not free (tx.Check).
func TestDeleteBucketNestedLeak(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()

	// A holds the nested buckets s1, s2, s3, each large enough to have pages of its own.
	err = db.Update(func(tx *bolt.Tx) error {
		a, err := tx.CreateBucket([]byte("A"))
		if err != nil {
			return err
		}
		for _, s := range []string{"s1", "s2", "s3"} {
			sb, err := a.CreateBucket([]byte(s))
			if err != nil {
				return err
			}
			for i := 0; i < 200; i++ {
				if err := sb.Put([]byte(fmt.Sprintf("k%04d", i)), make([]byte, 100)); err != nil {
					return err
				}
			}
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}

	// Write a key into A (this loads A's leaf into memory), then delete A.
	err = db.Update(func(tx *bolt.Tx) error {
		if err := tx.Bucket([]byte("A")).Put([]byte("z"), []byte("v")); err != nil {
			return err
		}
		return tx.DeleteBucket([]byte("A"))
	})
	if err != nil {
		t.Fatal(err)
	}

	err = db.View(func(tx *bolt.Tx) error {
		for e := range tx.Check() {
			t.Errorf("check: %v", e)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
}
