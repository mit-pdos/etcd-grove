package bbolt_test

import (
	"math"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
)

// A NaN FillPercent passes splitTwo's clamp; on amd64 int(pageSize*NaN) is
// MinInt64, a leaf is never split by size, and Commit panics with "inode
// overflow" at 65538 entries or more. (examples/axiomcx/bboltnan as a test of
// bbolt's own package directory.)
func TestBucket_FillPercentNaN(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	tx, err := db.Begin(true)
	if err != nil {
		t.Fatal(err)
	}
	b, err := tx.CreateBucketIfNotExists([]byte("b"))
	if err != nil {
		t.Fatal(err)
	}
	b.FillPercent = math.NaN()
	for i := uint64(0); i < 70000; i++ {
		if err := b.Put([]byte{byte(i >> 16), byte(i >> 8), byte(i)}, []byte{}); err != nil {
			t.Fatal(err)
		}
	}
	defer func() {
		if r := recover(); r != nil {
			// The writer lock is still held: do not Close the DB.
			t.Fatalf("Commit panicked: %v", r)
		}
	}()
	if err := tx.Commit(); err != nil {
		t.Fatal(err)
	}
	_ = db.Close()
}
