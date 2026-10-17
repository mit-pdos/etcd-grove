package mvcc

import (
	"fmt"
	"testing"
	"unsafe"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// reviewCheck compares the fast keys-only read with the full read over keys k0..k5 and the
// whole range, at every revision in [first, cur], through the read view r.
func reviewCheck(t *testing.T, rd func(key, end []byte, ro RangeOptions) (*RangeResult, error), first, cur int64, phase string) {
	t.Helper()
	revs := []int64{0} // 0: the view's current revision (a write txn's own changes)
	for rev := first; rev <= cur; rev++ {
		revs = append(revs, rev)
	}
	for _, rev := range revs {
		for _, kr := range [][2][]byte{{[]byte("k"), []byte("k\xff")}, {[]byte("k0"), nil}, {[]byte("k1"), nil}} {
			full, err := rd(kr[0], kr[1], RangeOptions{Rev: rev})
			if err != nil {
				t.Fatalf("%s: full at %d: %v", phase, rev, err)
			}
			fast, err := rd(kr[0], kr[1], RangeOptions{Rev: rev, FastKeysOnly: true})
			if err != nil {
				t.Fatalf("%s: fast at %d: %v", phase, rev, err)
			}
			if len(full.KVs) != len(fast.KVs) {
				t.Fatalf("%s: rev %d %q: %d full, %d fast", phase, rev, kr[0], len(full.KVs), len(fast.KVs))
			}
			for j := range full.KVs {
				f, g := full.KVs[j], fast.KVs[j]
				if string(f.Key) != string(g.Key) || f.ModRevision != g.ModRevision || f.CreateRevision != g.CreateRevision ||
					f.Version != g.Version || f.Lease != g.Lease {
					t.Errorf("%s: rev %d: fast %v, full %v", phase, rev, g, f)
				}
			}
		}
	}
}

// TestReviewLeaseSubRevisions: one write txn puts the same key several times with different
// leases (sub-revisions), deletes and re-creates another key with a new lease; keys-only reads
// inside the txn, after it, at the compaction revision itself, after a restart and after a
// snapshot Restore must give the full read's lease.
func TestReviewLeaseSubRevisions(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	defer b.Close()
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})

	s.Put([]byte("k1"), []byte("v"), 5)
	tw := s.Write(traceutil.TODO())
	tw.Put([]byte("k0"), []byte("v"), 1)
	tw.Put([]byte("k0"), []byte("v"), 2)
	// inside the write txn: the txn's own puts
	rdW := func(key, end []byte, ro RangeOptions) (*RangeResult, error) { return tw.Range(t.Context(), key, end, ro) }
	reviewCheck(t, rdW, tw.Rev(), tw.Rev(), "in-txn")
	tw.DeleteRange([]byte("k1"), nil)
	tw.Put([]byte("k1"), []byte("v"), 9)
	tw.Put([]byte("k0"), []byte("v"), 0)
	reviewCheck(t, rdW, tw.Rev(), tw.Rev(), "in-txn-2")
	if r, _ := tw.Range(t.Context(), []byte("k0"), nil, RangeOptions{FastKeysOnly: true}); len(r.KVs) != 1 || r.KVs[0].Lease != 0 || r.KVs[0].Version != 3 {
		t.Errorf("in-txn k0: %v", r.KVs)
	}
	if r, _ := tw.Range(t.Context(), []byte("k1"), nil, RangeOptions{FastKeysOnly: true}); len(r.KVs) != 1 || r.KVs[0].Lease != 9 {
		t.Errorf("in-txn k1: %v", r.KVs)
	}
	tw.End()
	s.Put([]byte("k0"), []byte("v"), 3)
	s.DeleteRange([]byte("k1"), nil) // k1 ends in a tombstone
	s.Put([]byte("k2"), []byte("v"), 4)
	s.DeleteRange([]byte("k2"), nil)

	rd := func(key, end []byte, ro RangeOptions) (*RangeResult, error) { return s.Range(t.Context(), key, end, ro) }
	reviewCheck(t, rd, 1, s.Rev(), "live")

	compactAt := s.Rev() - 1 // k2's put; k1's tombstone below it
	done, err := s.Compact(traceutil.TODO(), compactAt)
	if err != nil {
		t.Fatal(err)
	}
	<-done
	reviewCheck(t, rd, compactAt, s.Rev(), "compacted")
	s.Close()

	s = NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	rd = func(key, end []byte, ro RangeOptions) (*RangeResult, error) { return s.Range(t.Context(), key, end, ro) }
	reviewCheck(t, rd, compactAt, s.Rev(), "restarted")

	if err := s.Restore(b); err != nil {
		t.Fatal(err)
	}
	reviewCheck(t, rd, compactAt, s.Rev(), "snapshot-restored")
	s.Close()
}

// TestReviewRevisionLeaseSize reports the per-revision memory of the key index.
func TestReviewRevisionLeaseSize(t *testing.T) {
	t.Logf("sizeof Revision = %d, sizeof revisionLease = %d", unsafe.Sizeof(Revision{}), unsafe.Sizeof(revisionLease{}))
	_ = fmt.Sprint()
}
