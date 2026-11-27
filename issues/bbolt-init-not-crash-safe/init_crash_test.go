package bbolt_test

import (
	"bytes"
	"errors"
	"os"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
	berrors "go.etcd.io/bbolt/errors"
)

const initTestPageSize = 4096

// initImage returns the four pages a new database's initialization writes.
func initImage(t *testing.T) []byte {
	t.Helper()
	path := filepath.Join(t.TempDir(), "db")
	db, err := bolt.Open(path, 0o600, &bolt.Options{PageSize: initTestPageSize})
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Close(); err != nil {
		t.Fatal(err)
	}
	image, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if len(image) != 4*initTestPageSize {
		t.Fatalf("a new database is %d bytes, want four pages", len(image))
	}
	return image
}

// keep returns the image with the bytes keep rejects zeroed, cut to size bytes: the file a crash
// leaves when only some of an unsynced write's bytes reached the disk.
func keep(image []byte, size int, keep func(i int) bool) []byte {
	out := make([]byte, size)
	for i := 0; i < size; i++ {
		if keep(i) {
			out[i] = image[i]
		}
	}
	return out
}

func openAndUse(t *testing.T, path string) {
	t.Helper()
	db, err := bolt.Open(path, 0o600, &bolt.Options{PageSize: initTestPageSize})
	if err != nil {
		t.Fatalf("Open after an interrupted init: %v", err)
	}
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		return b.Put([]byte("k"), []byte("v"))
	}); err != nil {
		t.Fatal(err)
	}
	if err := db.Close(); err != nil {
		t.Fatal(err)
	}
	db, err = bolt.Open(path, 0o600, &bolt.Options{PageSize: initTestPageSize})
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	if err := db.View(func(tx *bolt.Tx) error {
		b := tx.Bucket([]byte("b"))
		if b == nil || !bytes.Equal(b.Get([]byte("k")), []byte("v")) {
			return errors.New("the committed key is missing")
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// A crash during a new database's initialization leaves part of its four pages: any subset of
// the bytes written since the last completed sync. Open initializes such a file again, so the
// database opens and works.
func TestOpen_InterruptedInit(t *testing.T) {
	const ps = initTestPageSize
	image := initImage(t)
	isMeta := func(i int) bool { return i < 2*ps }
	for _, tc := range []struct {
		name string
		file []byte
	}{
		// Before the first sync (the freelist and root pages, metas zero): any part of them.
		{"nothing-but-size", make([]byte, 4*ps)},
		{"first-page-only", make([]byte, ps)},
		{"data-pages-partial", keep(image, 3*ps+1, func(i int) bool { return !isMeta(i) })},
		{"data-pages-every-other-byte", keep(image, 4*ps, func(i int) bool { return !isMeta(i) && i%2 == 0 })},
		// Between the two syncs (the data pages synced, the metas written but not synced):
		// both meta pages torn.
		{"metas-torn-halves", keep(image, 4*ps, func(i int) bool { return !isMeta(i) || i%ps < 32 })},
		{"metas-torn-every-other-byte", keep(image, 4*ps, func(i int) bool { return !isMeta(i) || i%2 == 1 })},
		{"meta0-whole-meta1-torn", keep(image, 4*ps, func(i int) bool { return i < ps || i >= 2*ps || i%3 == 0 })},
		// The single unordered write of bbolt before this change: valid metas over a lost
		// freelist or root page (etcd-io/bbolt#567).
		{"metas-whole-freelist-lost", keep(image, 4*ps, func(i int) bool { return i < 2*ps || i >= 3*ps })},
		{"metas-whole-root-lost", keep(image, 4*ps, func(i int) bool { return i < 3*ps })},
		{"metas-whole-data-short", keep(image, 2*ps+100, func(i int) bool { return true })},
	} {
		t.Run(tc.name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "db")
			if err := os.WriteFile(path, tc.file, 0o600); err != nil {
				t.Fatal(err)
			}
			openAndUse(t, path)
		})
	}
}

// Open does not reinitialize a file holding a byte that initialization does not write: such a
// file is not one an interrupted initialization leaves, and is left unchanged.
func TestOpen_KeepsFileOutsideInitImage(t *testing.T) {
	const ps = initTestPageSize
	image := initImage(t)
	for _, tc := range []struct {
		name string
		file []byte
	}{
		{"stray-byte-in-root", func() []byte {
			f := keep(image, 4*ps, func(i int) bool { return i >= 2*ps })
			f[4*ps-1] = 0x7e
			return f
		}()},
		{"past-four-pages", make([]byte, 4*ps+1)},
		{"meta-of-another-txid", func() []byte {
			f := keep(image, 4*ps, func(i int) bool { return i >= 2*ps })
			f[16+48] = 2 // the low byte of meta 0's txid
			return f
		}()},
	} {
		t.Run(tc.name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "db")
			if err := os.WriteFile(path, tc.file, 0o600); err != nil {
				t.Fatal(err)
			}
			db, err := bolt.Open(path, 0o600, &bolt.Options{PageSize: ps})
			if err == nil {
				db.Close()
				t.Fatal("Open accepted a file outside the init image")
			}
			if !errors.Is(err, berrors.ErrInvalid) && !errors.Is(err, berrors.ErrChecksum) {
				t.Fatalf("Open returned %v", err)
			}
			after, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			if !bytes.Equal(tc.file, after) {
				t.Fatal("Open modified the file")
			}
		})
	}
}

// A database whose initialization completed, and one with committed data, open unchanged.
func TestOpen_CompletedInitNotReinitialized(t *testing.T) {
	path := filepath.Join(t.TempDir(), "db")
	openAndUse(t, path)
	before, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	db, err := bolt.Open(path, 0o600, &bolt.Options{PageSize: initTestPageSize})
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Close(); err != nil {
		t.Fatal(err)
	}
	after, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(before, after) {
		t.Fatal("Open rewrote a database with committed data")
	}
}
