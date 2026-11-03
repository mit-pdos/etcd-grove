package bbolt_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	bolt "go.etcd.io/bbolt"
	berrors "go.etcd.io/bbolt/errors"
	"go.etcd.io/bbolt/internal/btesting"
)

// Ensure that an error is returned when inserting a value of MaxValueSize
// bytes that is too large to be stored with its key. (The test of commit 1283e4e
// of fix/bbolt-max-value-size-unusable, as a file of its own.) Run one subtest at
// a time ('-run TestBucket_Put_MaxValueSizeWithKey/^a$', then /^ab$): the "ab"
// case panics the test binary. About 2 GB of memory each.
func TestBucket_Put_MaxValueSizeWithKey(t *testing.T) {
	for _, key := range []string{"a", "ab"} {
		t.Run(key, func(t *testing.T) {
			db := btesting.MustCreateDB(t)

			err := db.Update(func(tx *bolt.Tx) error {
				b, err := tx.CreateBucket([]byte("widgets"))
				require.NoError(t, err)
				return b.Put([]byte(key), make([]byte, bolt.MaxValueSize))
			})
			require.ErrorIs(t, err, berrors.ErrValueTooLarge)
		})
	}
}
