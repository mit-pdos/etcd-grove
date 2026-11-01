package bbolt

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

// With a large page size (Options.PageSize has no upper bound), a leaf of 65535 or more
// small entries fits one page, so spill does not split it, and node.write panics
// ("inode overflow": a page's element count is a uint16).
func TestReproLargePageInodeOverflow(t *testing.T) {
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, &Options{PageSize: 8 << 20})
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	err = db.Update(func(tx *Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		for i := 0; i < 70000; i++ {
			if err := b.Put([]byte(fmt.Sprintf("%06d", i)), []byte{1}); err != nil {
				return err
			}
		}
		return nil
	})
	t.Logf("Update returned %v", err)
}

// A page size above MaxAllocSize (2^31 - 1) is accepted, and the first commit's Tx.write
// panics giving its single-page buffer back to the pool (UnsafeByteSlice of pageSize bytes).
func TestReproPageSizeAboveMaxAlloc(t *testing.T) {
	if os.Getenv("BBOLT_REPRO_BIG") == "" {
		t.Skip("needs about 20 GiB of memory and 8 GiB of disk: set BBOLT_REPRO_BIG=1")
	}
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, &Options{PageSize: 1 << 31})
	if err != nil {
		t.Fatalf("Open: %v", err)
	}
	defer db.Close()
	t.Log("Open accepted a page size of 2^31")
	err = db.Update(func(tx *Tx) error {
		_, err := tx.CreateBucket([]byte("b"))
		return err
	})
	t.Logf("Update returned %v", err)
}
