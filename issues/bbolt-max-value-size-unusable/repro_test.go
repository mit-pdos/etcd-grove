package bbolt

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"
)

// A value of MaxValueSize bytes with a key of 2 bytes passes Put's checks, then Commit's
// node.write panics: WriteInodeToPage slices key+value bytes (2^31) out of a
// [MaxAllocSize]byte array (MaxAllocSize = 2^31 - 1 on amd64).
func TestReproMaxValueSizePanics(t *testing.T) {
	if os.Getenv("BBOLT_REPRO_BIG") == "" {
		t.Skip("needs about 6 GiB of memory: set BBOLT_REPRO_BIG=1")
	}
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	v := make([]byte, MaxValueSize)
	err = db.Update(func(tx *Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		if err := b.Put([]byte("ab"), v); err != nil {
			t.Logf("Put refused it: %v", err)
			return err
		}
		t.Log("Put accepted a 2-byte key with a MaxValueSize value; committing")
		return nil
	})
	t.Logf("Update returned %v", err)
}

// A leaf of at most four entries is never split, and WriteInodeToPage stores each element's
// position as a uint32: three values just under 2 GiB (each accepted by Put) put the third
// one's data past 4 GiB from its element, so its position wraps and a reader of the
// committed page reads the wrong bytes.
func TestReproLeafPosWraps(t *testing.T) {
	if os.Getenv("BBOLT_REPRO_BIG") == "" {
		t.Skip("needs about 20 GiB of memory and 6 GiB of disk: set BBOLT_REPRO_BIG=1")
	}
	db, err := Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	const n = 3
	vals := make([][]byte, n)
	for i := range vals {
		vals[i] = bytes.Repeat([]byte{byte('A' + i)}, MaxValueSize-16)
	}
	if err := db.Update(func(tx *Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		for i := 0; i < n; i++ {
			if err := b.Put([]byte{byte('a' + i)}, vals[i]); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatalf("Update: %v", err)
	}
	t.Log("committed three values of MaxValueSize-16 bytes")
	if err := db.View(func(tx *Tx) error {
		b := tx.Bucket([]byte("b"))
		for i := 0; i < n; i++ {
			got := b.Get([]byte{byte('a' + i)})
			if !bytes.Equal(got, vals[i]) {
				head := got
				if len(head) > 8 {
					head = head[:8]
				}
				t.Errorf("value %d read back wrong: len %d (want %d), starts %q (want %q...)",
					i, len(got), len(vals[i]), head, vals[i][:8])
			} else {
				t.Logf("value %d read back intact", i)
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}
