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

func TestOpen_PreservesUnrecognizedInitImage(t *testing.T) {
	const pageSize = 4096
	for _, tc := range []struct {
		name string
		size int
	}{
		{"nonempty-leaf", 4 * pageSize},
		{"past-last-init-page", 4*pageSize + 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "db")
			before := make([]byte, tc.size)
			before[len(before)-1] = 0x7e
			if err := os.WriteFile(path, before, 0o600); err != nil {
				t.Fatal(err)
			}
			db, err := bolt.Open(path, 0o600, &bolt.Options{PageSize: pageSize})
			if err == nil {
				db.Close()
				t.Fatal("Open initialized a file containing bytes outside its init image")
			}
			if !errors.Is(err, berrors.ErrInvalid) {
				t.Fatalf("Open returned %v, want ErrInvalid", err)
			}
			after, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			if !bytes.Equal(before, after) {
				t.Fatal("Open modified the unrecognized file")
			}
		})
	}
}

func TestOpen_RecoversPartialInitDataPages(t *testing.T) {
	const pageSize = 8192
	opts := &bolt.Options{PageSize: pageSize}
	path := filepath.Join(t.TempDir(), "db")
	db, err := bolt.Open(path, 0o600, opts)
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
	clear(image[:2*pageSize])
	// Only page 2 and the start of page 3 made it to disk.
	if err := os.WriteFile(path, image[:3*pageSize+1], 0o600); err != nil {
		t.Fatal(err)
	}
	db, err = bolt.Open(path, 0o600, opts)
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Update(func(tx *bolt.Tx) error {
		_, err := tx.CreateBucket([]byte("recovered"))
		return err
	}); err != nil {
		t.Fatal(err)
	}
	if err := db.Close(); err != nil {
		t.Fatal(err)
	}
}
