package bbolt_test

import (
	"bytes"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
)

// The Tx.CreateBucket / CreateBucketIfNotExists documentation: "Returns an error if the bucket
// name is blank, or if the bucket name is too long."
func TestLongBucketName(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	for _, n := range []int{bolt.MaxKeySize + 1, 1 << 20} {
		name := bytes.Repeat([]byte("n"), n)
		err = db.Update(func(tx *bolt.Tx) error {
			_, err := tx.CreateBucket(name)
			return err
		})
		if err == nil {
			t.Errorf("CreateBucket accepted a %d-byte name (MaxKeySize %d)", len(name), bolt.MaxKeySize)
		}
		err = db.Update(func(tx *bolt.Tx) error {
			_, err := tx.CreateBucketIfNotExists(append(name, 'x'))
			return err
		})
		if err == nil {
			t.Errorf("CreateBucketIfNotExists accepted a %d-byte name (MaxKeySize %d)", len(name)+1, bolt.MaxKeySize)
		}
	}
	_ = db.View(func(tx *bolt.Tx) error {
		if tx.Bucket(bytes.Repeat([]byte("n"), 1<<20)) == nil {
			t.Errorf("the 1 MiB bucket is not readable back")
		}
		return nil
	})
}
