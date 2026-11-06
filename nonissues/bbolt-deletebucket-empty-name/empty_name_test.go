package bbolt_test

import (
	"errors"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
	berrors "go.etcd.io/bbolt/errors"
)

func TestDeleteBucketEmptyName(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	_ = db.Update(func(tx *bolt.Tx) error {
		err := tx.DeleteBucket([]byte{})
		t.Logf("empty root: %v (notfound=%v incompatible=%v)", err, errors.Is(err, berrors.ErrBucketNotFound), errors.Is(err, berrors.ErrIncompatibleValue))
		if _, err := tx.CreateBucket([]byte("a")); err != nil {
			t.Fatal(err)
		}
		err = tx.DeleteBucket([]byte{})
		t.Logf("nonempty root: %v", err)
		return nil
	})
}
