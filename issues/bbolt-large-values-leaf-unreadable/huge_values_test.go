package bbolt_test

import (
	"bytes"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	bolt "go.etcd.io/bbolt"
	"go.etcd.io/bbolt/internal/common"
)

// Two values of MaxAllocSize/2 bytes committed together land on one leaf page
// (a leaf of at most four keys is never split), and Get of the second panics.
// About 5 GB of memory. (The end-to-end test of the issue draft; the branch
// fix/bbolt-large-values-leaf-unreadable tests the split instead,
// TestNode_split_MaxAllocSize.)
func TestDB_HugeValues(t *testing.T) {
	dbPath := filepath.Join(t.TempDir(), "db")
	db, err := bolt.Open(dbPath, 0600, nil)
	require.NoError(t, err)
	defer func() {
		require.NoError(t, db.Close())
	}()

	keys := []string{"a", "b"}
	values := make([][]byte, len(keys))
	for i := range values {
		values[i] = make([]byte, common.MaxAllocSize/2)
		values[i][len(values[i])-1] = keys[i][0]
	}

	err = db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("data"))
		require.NoError(t, err)
		for i, key := range keys {
			require.NoError(t, b.Put([]byte(key), values[i]))
		}
		return nil
	})
	require.NoError(t, err)

	err = db.View(func(tx *bolt.Tx) error {
		b := tx.Bucket([]byte("data"))
		for i, key := range keys {
			require.Truef(t, bytes.Equal(values[i], b.Get([]byte(key))), "unexpected value for key %q", key)
		}
		return nil
	})
	require.NoError(t, err)
}
