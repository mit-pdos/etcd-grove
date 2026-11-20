package foreachkv

// The independent attack's tests of the path `First` adds over `Seek` (auth-schema-srv A2, 2026-11-17,
// /shared/tmp/foreach-attack/report.md, family 4): `first()` (cursor.go:44-62) skips an empty leaf
// through `next()` (cursor.go:215-247), so a write transaction's own deletes that empty whole leaves or
// subtrees leave the walk equal to the sorted contents (`ForEach_kvw`'s `bktEnts m`).

import (
	"bytes"
	"fmt"
	"math/rand"
	"path/filepath"
	"sort"
	"testing"

	bolt "go.etcd.io/bbolt"
)

func bigKey(i int) []byte { return []byte(fmt.Sprintf("k%08d", i)) }

func openBig(t *testing.T, n, vlen int) *bolt.DB {
	t.Helper()
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, &bolt.Options{InitialMmapSize: 1 << 30, NoSync: true})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { db.Close() })
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket(bkt)
		if err != nil {
			return err
		}
		for i := 0; i < n; i++ {
			if err := b.Put(bigKey(i), bytes.Repeat([]byte{byte(i)}, vlen)); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	return db
}

func walkKeys(b *bolt.Bucket) ([]string, error) {
	var out []string
	err := b.ForEach(func(k, v []byte) error {
		if k == nil {
			panic("nil key")
		}
		out = append(out, string(k))
		return nil
	})
	return out, err
}

// Family 4/6: write tx with deletes emptying whole leaves (first, middle, last, whole subtrees)
// and puts into deleted ranges; ForEach (First, not Seek) must walk exactly the model's sorted keys.
func TestWriteTxEmptyLeaves(t *testing.T) {
	for seed := int64(0); seed < 40; seed++ {
		n := 30000
		vlen := 1 + int(seed%5)*40
		db := openBig(t, n, vlen)
		r := rand.New(rand.NewSource(seed))
		model := map[string]bool{}
		for i := 0; i < n; i++ {
			model[string(bigKey(i))] = true
		}
		if err := db.Update(func(tx *bolt.Tx) error {
			b := tx.Bucket(bkt)
			// delete random ranges, including prefix and suffix
			ranges := [][2]int{{0, r.Intn(8000) + 1}, {n - r.Intn(8000) - 1, n}}
			for j := 0; j < 5; j++ {
				a := r.Intn(n)
				ranges = append(ranges, [2]int{a, a + r.Intn(6000)})
			}
			for _, rg := range ranges {
				for i := rg[0]; i < rg[1] && i < n; i++ {
					if err := b.Delete(bigKey(i)); err != nil {
						return err
					}
					delete(model, string(bigKey(i)))
				}
			}
			// some puts back into deleted ranges
			for j := 0; j < 50; j++ {
				i := r.Intn(n)
				if err := b.Put(bigKey(i), []byte("new")); err != nil {
					return err
				}
				model[string(bigKey(i))] = true
			}
			got, err := walkKeys(b)
			if err != nil {
				return err
			}
			var exp []string
			for k := range model {
				exp = append(exp, k)
			}
			sort.Strings(exp)
			if len(got) != len(exp) {
				t.Fatalf("seed %d: got %d entries, model %d", seed, len(got), len(exp))
			}
			for i := range got {
				if got[i] != exp[i] {
					t.Fatalf("seed %d: entry %d: %q vs %q", seed, i, got[i], exp[i])
				}
			}
			return nil
		}); err != nil {
			t.Fatal(err)
		}
	}
}

// Delete every key in a write tx, then ForEach: no visit.
func TestWriteTxAllDeleted(t *testing.T) {
	db := openBig(t, 20000, 100)
	db.Update(func(tx *bolt.Tx) error {
		b := tx.Bucket(bkt)
		for i := 0; i < 20000; i++ {
			b.Delete(bigKey(i))
		}
		got, _ := walkKeys(b)
		if len(got) != 0 {
			t.Fatalf("got %d", len(got))
		}
		// and a single put in the middle
		b.Put(bigKey(12345), nil)
		got, _ = walkKeys(b)
		if len(got) != 1 || got[0] != string(bigKey(12345)) {
			t.Fatalf("got %v", got)
		}
		return nil
	})
}
