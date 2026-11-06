package bbolt

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

// A database restored from Tx.WriteTo whose transaction id is odd has its
// current meta on page 0, the page the next commit writes. Two consecutive
// commits whose meta write is torn (part of the page written, then an I/O
// error) then destroy both metas, and the second commit's rollback panics in
// db.meta(). A database that bbolt itself committed survives the same two
// faults, which the control below checks.
func TestWriteTo_OddTxid_TornMetaWrites(t *testing.T) {
	for _, restored := range []bool{false, true} {
		t.Run(fmt.Sprintf("restored=%v", restored), func(t *testing.T) {
			dir := t.TempDir()
			src := filepath.Join(dir, "src.db")
			db, err := Open(src, 0600, nil)
			if err != nil {
				t.Fatal(err)
			}
			// Two commits: the current txid becomes 3 (odd).
			for i := 0; i < 2; i++ {
				if err := db.Update(func(tx *Tx) error {
					b, err := tx.CreateBucketIfNotExists([]byte("b"))
					if err != nil {
						return err
					}
					return b.Put([]byte(fmt.Sprintf("k%d", i)), []byte("v"))
				}); err != nil {
					t.Fatal(err)
				}
			}
			path := src
			if restored {
				path = filepath.Join(dir, "snap.db")
				f, err := os.Create(path)
				if err != nil {
					t.Fatal(err)
				}
				if err := db.View(func(tx *Tx) error {
					if tx.ID()%2 != 1 {
						t.Fatalf("txid %d not odd", tx.ID())
					}
					_, err := tx.WriteTo(f)
					return err
				}); err != nil {
					t.Fatal(err)
				}
				if err := f.Close(); err != nil {
					t.Fatal(err)
				}
			}
			if err := db.Close(); err != nil {
				t.Fatal(err)
			}

			db, err = Open(path, 0600, nil)
			if err != nil {
				t.Fatal(err)
			}
			panicked := false
			defer func() {
				// After the panic the writer lock is still held: Close would block.
				if !panicked {
					_ = db.Close()
				}
			}()

			// Tear every meta write: write the meta through its txid (72 bytes:
			// the 16-byte page header and the meta up to its checksum), then fail.
			ps := int64(db.pageSize)
			realWriteAt := db.ops.writeAt
			db.ops.writeAt = func(b []byte, off int64) (int, error) {
				if off < 2*ps && len(b) == int(ps) {
					n, _ := realWriteAt(b[:72], off)
					return n, errors.New("injected: torn meta write")
				}
				return realWriteAt(b, off)
			}

			for i := 0; i < 2 && !panicked; i++ {
				func() {
					defer func() {
						if r := recover(); r != nil {
							panicked = true
							t.Errorf("commit %d after a torn meta write panicked: %v", i+1, r)
						}
					}()
					err := db.Update(func(tx *Tx) error {
						return tx.Bucket([]byte("b")).Put([]byte("x"), []byte("y"))
					})
					if err == nil {
						t.Fatalf("commit %d: expected the injected error", i+1)
					}
				}()
			}
		})
	}
}
