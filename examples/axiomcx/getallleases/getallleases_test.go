// Package getallleases holds the Go checks of the axiom review of
// schema.MustUnsafeGetAllLeases (notes/axiom-review/getallleases.md): tests only, no Goose project.
package getallleases

import (
	"bytes"
	"encoding/binary"
	"sort"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease/leasepb"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func newBackend(t *testing.T) backend.Backend {
	be := backend.NewDefaultBackend(zap.NewNop(), t.TempDir()+"/db")
	t.Cleanup(func() { be.Close() })
	return be
}

func key(id int64) []byte {
	b := make([]byte, 8)
	binary.BigEndian.PutUint64(b, uint64(id))
	return b
}

// TestMissingBucket: no Lease bucket at all (UnsafeCreateLeaseBucket not called): no panic, an
// empty non-nil slice (the spec: bktOf of an absent bucket is empty, recs = []).
func TestMissingBucket(t *testing.T) {
	be := newBackend(t)
	tx := be.BatchTx()
	tx.Lock()
	ls := schema.MustUnsafeGetAllLeases(tx)
	tx.Unlock()
	if ls == nil || len(ls) != 0 {
		t.Fatalf("got %v", ls)
	}
}

// TestEmptyBucket: the bucket created, nothing in it.
func TestEmptyBucket(t *testing.T) {
	be := newBackend(t)
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateLeaseBucket(tx)
	schema.UnsafeCreateLeaseBucket(tx) // twice: no panic
	ls := schema.MustUnsafeGetAllLeases(tx)
	tx.Unlock()
	if ls == nil || len(ls) != 0 {
		t.Fatalf("got %v", ls)
	}
}

var recs = [][3]int64{
	{5, 10, 3},
	{-1, 1, 0},                      // key ff..ff: last in unsigned byte order, first in signed order
	{0x100, 7, 7},                   // key 00..0100: after 5 numerically, before it if compared by length/LE
	{1, -5, -9},                     // negative TTLs: 10-byte varints
	{0, 0, 0},                       // all-zero message: the empty encoding (an empty bbolt value)
	{-0x7fffffffffffffff - 1, 2, 2}, // key 80 00..: middle of the unsigned order
}

// expected: the records sorted by their keys as unsigned bytes (bbolt's order, GoStringLt).
func expected() [][3]int64 {
	out := append([][3]int64(nil), recs...)
	sort.Slice(out, func(i, j int) bool { return bytes.Compare(key(out[i][0]), key(out[j][0])) < 0 })
	return out
}

func check(t *testing.T, where string, ls []*leasepb.Lease) {
	t.Helper()
	exp := expected()
	if len(ls) != len(exp) {
		t.Fatalf("%s: %d leases, want %d", where, len(ls), len(exp))
	}
	seen := map[*leasepb.Lease]bool{}
	for i, l := range ls {
		if seen[l] {
			t.Fatalf("%s: pointer %d repeated", where, i)
		}
		seen[l] = true
		if l.ID != exp[i][0] || l.TTL != exp[i][1] || l.RemainingTTL != exp[i][2] {
			t.Fatalf("%s: lease %d = (%d,%d,%d), want %v", where, i, l.ID, l.TTL, l.RemainingTTL, exp[i])
		}
	}
}

func putAll(tx backend.BatchTx) {
	for _, r := range recs {
		schema.MustUnsafePutLease(tx, &leasepb.Lease{ID: r[0], TTL: r[1], RemainingTTL: r[2]})
	}
}

// TestOrderAndValues: the records in key order (unsigned bytes), with their fields, read through
// the writer before any commit (uncommitted writes visible), and after a commit and a reopen.
func TestOrderAndValues(t *testing.T) {
	dir := t.TempDir()
	be := backend.NewDefaultBackend(zap.NewNop(), dir+"/db")
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateLeaseBucket(tx)
	putAll(tx)
	check(t, "uncommitted", schema.MustUnsafeGetAllLeases(tx))
	tx.Unlock()
	be.ForceCommit()
	tx.Lock()
	check(t, "committed", schema.MustUnsafeGetAllLeases(tx))
	tx.Unlock()
	be.Close()
	be = backend.NewDefaultBackend(zap.NewNop(), dir+"/db")
	defer be.Close()
	tx = be.BatchTx()
	tx.Lock()
	check(t, "reopened", schema.MustUnsafeGetAllLeases(tx))
	tx.Unlock()
}

// TestNoAliasing: the returned messages share no memory with bbolt's pages: rewrite every record,
// delete some, grow the database past several remaps, commit; the old results are unchanged. And
// writing the results changes nothing in the bucket.
func TestNoAliasing(t *testing.T) {
	be := newBackend(t)
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateLeaseBucket(tx)
	putAll(tx)
	tx.Unlock()
	be.ForceCommit()
	tx.Lock()
	ls := schema.MustUnsafeGetAllLeases(tx)
	ls2 := schema.MustUnsafeGetAllLeases(tx)
	for _, l := range ls2 {
		l.ID, l.TTL, l.RemainingTTL = 42, 42, 42 // the second read's messages: fresh
	}
	for _, r := range recs {
		schema.MustUnsafePutLease(tx, &leasepb.Lease{ID: r[0], TTL: r[1] + 1000, RemainingTTL: 99})
	}
	tx.Unlock()
	be.ForceCommit()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Key)
	tx.Unlock()
	big := make([]byte, 64*1024)
	for i := 0; i < 2000; i++ { // ~128 MB: several mmap remaps
		tx.Lock()
		tx.UnsafePut(schema.Key, key(int64(i)), big)
		tx.Unlock()
		if i%100 == 0 {
			be.ForceCommit()
		}
	}
	be.ForceCommit()
	check(t, "first read after rewrite and remap", ls)
	tx.Lock()
	for _, r := range recs {
		schema.UnsafeDeleteLease(tx, &leasepb.Lease{ID: r[0]})
	}
	ls3 := schema.MustUnsafeGetAllLeases(tx)
	tx.Unlock()
	if len(ls3) != 0 {
		t.Fatalf("after deletes: %d", len(ls3))
	}
	check(t, "first read after delete", ls)
}

// TestUndecodable: the premise is needed: a value that does not decode panics (what the premise
// "every value is leaseEnc" excludes). Not a counterexample: no proof can establish the premise
// for these bytes (leaseEnc is opaque).
func TestUndecodable(t *testing.T) {
	be := newBackend(t)
	tx := be.BatchTx()
	tx.Lock()
	defer tx.Unlock()
	schema.UnsafeCreateLeaseBucket(tx)
	tx.UnsafePut(schema.Lease, key(3), []byte{0xff})
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("no panic")
		}
		t.Logf("panics as expected: %v", r)
	}()
	schema.MustUnsafeGetAllLeases(tx)
}

// TestOddKeysDecodable: a key that is not 8 bytes, or not the id's bytes, with a decodable value:
// no panic (bytesToLeaseID is called only on a decode error). The premise excludes these states
// anyway (keys are the ids' bytes).
func TestOddKeysDecodable(t *testing.T) {
	be := newBackend(t)
	tx := be.BatchTx()
	tx.Lock()
	defer tx.Unlock()
	schema.UnsafeCreateLeaseBucket(tx)
	tx.UnsafePut(schema.Lease, []byte{1, 2, 3}, []byte{})
	tx.UnsafePut(schema.Lease, key(9), []byte{0x08, 0x07}) // ID 7 under the key of 9
	ls := schema.MustUnsafeGetAllLeases(tx)
	if len(ls) != 2 || ls[0].ID != 7 || ls[1].ID != 0 {
		t.Fatalf("got %v", ls)
	}
}

// TestUnknownFields: a value with an unknown field decodes (the unknown bytes kept in the
// message, copied: then rewritten and remapped, the message is unchanged). Not reachable through
// MustUnsafePutLease's spec (unknownFields' = nil).
func TestUnknownFields(t *testing.T) {
	be := newBackend(t)
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateLeaseBucket(tx)
	tx.UnsafePut(schema.Lease, key(4), []byte{0x08, 0x04, 0x22, 0x02, 'h', 'i'}) // ID 4, field 4 "hi"
	ls := schema.MustUnsafeGetAllLeases(tx)
	tx.UnsafePut(schema.Lease, key(4), []byte{0x08, 0x04, 0x22, 0x02, 'x', 'x'})
	tx.Unlock()
	be.ForceCommit()
	if len(ls) != 1 || ls[0].ID != 4 || !bytes.Equal(ls[0].ProtoReflect().GetUnknown(), []byte{0x22, 0x02, 'h', 'i'}) {
		t.Fatalf("got %v", ls)
	}
}

// TestAfterClose: Lock and MustUnsafeGetAllLeases after Close (excluded by the specs: Lock takes
// bOpen, Close all of it). Recorded for the report.
func TestAfterClose(t *testing.T) {
	be := backend.NewDefaultBackend(zap.NewNop(), t.TempDir()+"/db")
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateLeaseBucket(tx)
	tx.Unlock()
	be.Close()
	defer func() { t.Logf("after Close: recover() = %v", recover()) }()
	tx.Lock()
	ls := schema.MustUnsafeGetAllLeases(tx)
	t.Logf("after Close: no panic, %d leases", len(ls))
}
