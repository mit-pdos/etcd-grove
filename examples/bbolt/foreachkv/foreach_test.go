// Package foreachkv backs the trust-boundary axioms bbolt.Bucket.ForEach_kvr / ForEach_kvw
// (Spec/go_etcd_io/bbolt/Bucket__ForEach_kv{r,w}.lean; auth-schema-srv A2, 2026-11-17): each test
// is one claim of the axioms, or one behaviour they must exclude (bbolt v1.5.0, bucket.go:585-596,
// cursor.go:32-42).
package foreachkv

import (
	"bytes"
	"errors"
	"fmt"
	"path/filepath"
	"strings"
	"testing"

	bolt "go.etcd.io/bbolt"
	berrors "go.etcd.io/bbolt/errors"
)

var bkt = []byte("b")

func openDB(t *testing.T, keys ...string) *bolt.DB {
	t.Helper()
	db, err := bolt.Open(filepath.Join(t.TempDir(), "db"), 0600, nil)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { db.Close() })
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket(bkt)
		if err != nil {
			return err
		}
		for _, k := range keys {
			if err := b.Put([]byte(k), []byte("v"+k)); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	return db
}

type kv struct{ k, v string }

func walk(b *bolt.Bucket) ([]kv, error) {
	var got []kv
	err := b.ForEach(func(k, v []byte) error {
		if k == nil {
			return fmt.Errorf("nil key")
		}
		got = append(got, kv{string(k), string(v)})
		return nil
	})
	return got, err
}

func want(keys ...string) []kv {
	var w []kv
	for _, k := range keys {
		w = append(w, kv{k, "v" + k})
	}
	return w
}

func same(a, b []kv) bool { return fmt.Sprint(a) == fmt.Sprint(b) }

// Claim (both axioms, post `I es.length`): the visitor is called once per entry, in key order
// (`bktEnts`, sorted), with a non-nil key and the entry's key and value, and ForEach returns nil.
func TestOrderReadTx(t *testing.T) {
	db := openDB(t, "c", "a", "b", "aa", "\x00", "zz")
	if err := db.View(func(tx *bolt.Tx) error {
		got, err := walk(tx.Bucket(bkt))
		if err != nil {
			return err
		}
		if w := want("\x00", "a", "aa", "b", "c", "zz"); !same(got, w) {
			return fmt.Errorf("got %q, want %q", got, w)
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// Claim (ForEach_kvw: the entries are `bktEnts m` of the transaction's contents `S` now): in the write
// transaction the walk sees the transaction's own uncommitted puts and deletes.
func TestOrderWriteTxSeesOwnWrites(t *testing.T) {
	db := openDB(t, "a", "c")
	if err := db.Update(func(tx *bolt.Tx) error {
		b := tx.Bucket(bkt)
		if err := b.Put([]byte("b"), []byte("vb")); err != nil {
			return err
		}
		if err := b.Delete([]byte("c")); err != nil {
			return err
		}
		got, err := walk(b)
		if err != nil {
			return err
		}
		if w := want("a", "b"); !same(got, w) {
			return fmt.Errorf("got %q, want %q", got, w)
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// Claim (`es = []`: `I 0` back, nil): an empty bucket calls no visitor.
func TestEmpty(t *testing.T) {
	db := openDB(t)
	if err := db.View(func(tx *bolt.Tx) error {
		got, err := walk(tx.Bucket(bkt))
		if err != nil || len(got) != 0 {
			return fmt.Errorf("got %q, %v", got, err)
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// Claim (post's error branch `E i err`): the first visitor error stops the walk (no later entry is
// visited) and is returned unchanged.
func TestErrorStops(t *testing.T) {
	db := openDB(t, "a", "b", "c", "d")
	sentinel := errors.New("stop")
	if err := db.View(func(tx *bolt.Tx) error {
		var seen []string
		err := tx.Bucket(bkt).ForEach(func(k, v []byte) error {
			seen = append(seen, string(k))
			if string(k) == "b" {
				return sentinel
			}
			return nil
		})
		if err != sentinel {
			return fmt.Errorf("returned %v, want the visitor's error", err)
		}
		if strings.Join(seen, ",") != "a,b" {
			return fmt.Errorf("visited %v after the error", seen)
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// Excluded (`txLive tx q` in the pre): on a closed transaction ForEach returns ErrTxClosed without
// visiting (the `b.tx.db == nil` branch).
func TestClosedTx(t *testing.T) {
	db := openDB(t, "a")
	tx, err := db.Begin(false)
	if err != nil {
		t.Fatal(err)
	}
	b := tx.Bucket(bkt)
	if err := tx.Rollback(); err != nil {
		t.Fatal(err)
	}
	called := false
	err = b.ForEach(func(k, v []byte) error { called = true; return nil })
	if !errors.Is(err, berrors.ErrTxClosed) || called {
		t.Fatalf("got %v, called %v; want ErrTxClosed", err, called)
	}
}

// Excluded (the visitor gets only half of the walk's `txLive`, so it cannot meet `Tx.Rollback_kv`'s
// `txLive tx 1`): a visitor that closes the read transaction makes the walk panic at the next entry.
func TestVisitorRollbackPanics(t *testing.T) {
	db := openDB(t, "a", "b")
	tx, err := db.Begin(false)
	if err != nil {
		t.Fatal(err)
	}
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("ForEach returned; expected a panic")
		}
		t.Logf("ForEach panicked: %v", r)
	}()
	tx.Bucket(bkt).ForEach(func(k, v []byte) error { return tx.Rollback() })
}

// Excluded (ForEach_kvw holds `ownWTxG` during the walk, so the visitor cannot `Delete`): deleting
// the current key from the visitor skips the next entry ("The provided function must not modify the
// bucket; this will result in undefined behavior.", bucket.go).
func TestVisitorDeleteSkips(t *testing.T) {
	db := openDB(t, "a", "b", "c", "d")
	if err := db.Update(func(tx *bolt.Tx) error {
		b := tx.Bucket(bkt)
		// materialize the leaf (a write transaction's cursor then walks the node the visitor changes)
		if err := b.Put([]byte("a"), []byte("va")); err != nil {
			return err
		}
		var seen []string
		if err := b.ForEach(func(k, v []byte) error {
			seen = append(seen, string(k))
			return b.Delete(k)
		}); err != nil {
			return err
		}
		if strings.Join(seen, ",") == "a,b,c,d" {
			return fmt.Errorf("visited every entry; expected skips")
		}
		t.Logf("visited %v of a,b,c,d", seen)
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// Excluded (as above, `Put`): a key put by the visitor after the cursor's position is visited, so
// the walk is not over the entries it started with (with the leaf materialized; on an unmaterialized
// page the cursor keeps walking the old page and the put is not visited: either way the visitor's
// writes make the walk depend on bbolt's internals).
func TestVisitorPutVisited(t *testing.T) {
	db := openDB(t, "a", "c")
	if err := db.Update(func(tx *bolt.Tx) error {
		b := tx.Bucket(bkt)
		// materialize the leaf (a write transaction's cursor then walks the node the visitor changes)
		if err := b.Put([]byte("a"), []byte("va")); err != nil {
			return err
		}
		var seen []string
		if err := b.ForEach(func(k, v []byte) error {
			seen = append(seen, string(k))
			if bytes.Equal(k, []byte("a")) {
				return b.Put([]byte("b"), []byte("vb"))
			}
			return nil
		}); err != nil {
			return err
		}
		if strings.Join(seen, ",") != "a,b,c" {
			return fmt.Errorf("visited %v", seen)
		}
		t.Logf("visited %v: the visitor's put is walked", seen)
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}

// Not excluded by Go, excluded conservatively by ForEach_kvr (it holds `rtxStats` during the walk):
// a nested walk of the same read transaction works in Go.
func TestNestedReadWalkWorks(t *testing.T) {
	db := openDB(t, "a", "b")
	if err := db.View(func(tx *bolt.Tx) error {
		n := 0
		err := tx.Bucket(bkt).ForEach(func(k, v []byte) error {
			got, err := walk(tx.Bucket(bkt))
			n += len(got)
			return err
		})
		if err != nil || n != 4 {
			return fmt.Errorf("nested: %v, %d", err, n)
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
}
