package bbolt_test

import (
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	bolt "go.etcd.io/bbolt"
)

// A put and a read in one bucket, the smallest use of bbolt. Run under
// GOARCH=386 (or any 32-bit platform): Tx's statistics are updated with 64-bit
// atomics, which panic when Tx.stats is not 8-byte aligned.
func TestTx_Stats_Aligned32Bit(t *testing.T) {
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	require.NoError(t, err)
	defer db.Close()

	require.NoError(t, db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		return b.Put([]byte("k"), []byte("v"))
	}))
	require.NoError(t, db.View(func(tx *bolt.Tx) error {
		require.Equal(t, []byte("v"), tx.Bucket([]byte("b")).Get([]byte("k")))
		return nil
	}))
}
