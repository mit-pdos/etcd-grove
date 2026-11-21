package bbolt_test

import (
	"bytes"
	"os"
	"testing"

	"github.com/stretchr/testify/require"

	bolt "go.etcd.io/bbolt"
	"go.etcd.io/bbolt/internal/btesting"
	"go.etcd.io/bbolt/internal/common"
)

// An entry just above the former 256 MiB cap fits in a leaf on 64-bit platforms.
func TestBucket_Put_LargeReadableEntry(t *testing.T) {
	const size = 1 << 28
	if common.MaxAllocSize <= size || os.Getenv("DRONE") == "true" {
		t.Skip("requires a 64-bit address space and large database file")
	}
	db := btesting.MustCreateDB(t)
	key := []byte("foo")
	value := make([]byte, size)
	value[size-1] = 83
	require.NoError(t, db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("widgets"))
		if err != nil {
			return err
		}
		return b.Put(key, value)
	}))
	require.NoError(t, db.View(func(tx *bolt.Tx) error {
		require.True(t, bytes.Equal(value, tx.Bucket([]byte("widgets")).Get(key)))
		return nil
	}))
}
