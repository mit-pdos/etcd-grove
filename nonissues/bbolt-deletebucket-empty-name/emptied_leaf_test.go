package bbolt_test

import (
	"errors"
	"fmt"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
	berrors "go.etcd.io/bbolt/errors"
)

// TestDeleteBucketEmptyNameEmptiedLeaf: a write transaction that deleted every bucket of the
// root's first leaf gets ErrIncompatibleValue from DeleteBucket of the empty name, although the
// root still holds buckets.
func TestDeleteBucketEmptyNameEmptiedLeaf(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	if err := db.Update(func(tx *bolt.Tx) error {
		for i := 0; i < 2000; i++ {
			if _, err := tx.CreateBucket([]byte(fmt.Sprintf("bucket-%06d", i))); err != nil {
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
	for i := 0; i < 50; i++ { // the first leaf's buckets
		if err := tx.DeleteBucket([]byte(fmt.Sprintf("bucket-%06d", i))); err != nil {
			t.Fatal(err)
		}
	}
	k, _ := tx.Cursor().First()
	err = tx.DeleteBucket([]byte{})
	t.Logf("first remaining %q; DeleteBucket(\"\") = %v (notfound=%v incompatible=%v)", k, err,
		errors.Is(err, berrors.ErrBucketNotFound), errors.Is(err, berrors.ErrIncompatibleValue))
}
