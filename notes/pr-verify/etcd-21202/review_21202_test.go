// Reviewer tests for etcd-io/etcd#21202 (package mvcc, PR head a9522b154).

package mvcc

import (
	"errors"
	"fmt"
	"math"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func newRStore(t *testing.T) (*store, backend.Backend) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	t.Cleanup(func() { cleanup(s, b) })
	return s, b
}

// R1: a value that does not decode as a KeyValue is left out of the detailed mode's
// total hash (and per-key list), but is in the plain mode's hash: the two modes
// disagree exactly on the corrupted data a hash comparison is meant to find.
func TestReviewDetailedDropsUndecodableValue(t *testing.T) {
	s, b := newRStore(t)
	s.Put([]byte("foo"), []byte("v2"), lease.NoLease) // 2
	s.Put([]byte("bar"), []byte("v3"), lease.NoLease) // 3

	before, _, _ := s.HashStorage().HashByRev(0)
	// Corrupt the value stored at revision 3.
	tx := b.BatchTx()
	tx.Lock()
	key := BucketKeyToBytes(newBucketKey(3, 0, false), NewRevBytes())
	tx.UnsafePut(schema.Key, key, []byte{0xff, 0xff, 0xff})
	tx.Unlock()
	b.ForceCommit()

	plain, _, err1 := s.HashStorage().HashByRev(0)
	det, _, err2 := s.HashStorage().HashByRevDetailed(0, 0)
	t.Logf("before corruption: %+v", before)
	t.Logf("plain after corruption: %+v err=%v", plain, err1)
	t.Logf("detailed total after corruption: %+v err=%v keys=%+v", det.TotalHash, err2, det.KeyHashes)
	if plain.Hash != det.TotalHash.Hash {
		t.Errorf("plain hash %d != detailed total hash %d on the same store (undecodable value at rev 3 skipped by detailed mode)", plain.Hash, det.TotalHash.Hash)
	}
}

// R2: --compact-rev MaxInt64 with --rev 0 is accepted and overflows the hasher's
// lower bound (compactRevision + 1): the keep filter is switched off and every
// revision is hashed, so MaxInt64 gives the hash of compactRev 0 on an uncompacted
// store, while MaxInt64-1 hashes only the live revisions.
func TestReviewCompactRevMaxInt64Overflow(t *testing.T) {
	s, _ := newRStore(t)
	for i := 2; i <= 6; i++ {
		s.Put([]byte("foo"), []byte(fmt.Sprintf("v%d", i)), lease.NoLease)
	}
	hs := s.HashStorage()
	h0, _, e0 := hs.HashByRevWithCompactRev(0, 0)
	hMax, _, eMax := hs.HashByRevWithCompactRev(0, math.MaxInt64)
	hMax1, _, eMax1 := hs.HashByRevWithCompactRev(0, math.MaxInt64-1)
	t.Logf("compactRev 0: %+v %v", h0, e0)
	t.Logf("compactRev MaxInt64: %+v %v", hMax, eMax)
	t.Logf("compactRev MaxInt64-1: %+v %v", hMax1, eMax1)
	if hMax.Hash == h0.Hash && hMax.Hash != hMax1.Hash {
		t.Errorf("compactRev MaxInt64 hashes every revision (== compactRev 0: %d), MaxInt64-1 only the live ones (%d): overflow of compactRevision+1", h0.Hash, hMax1.Hash)
	}
}

// R3: "revisions less than or equal to this value will be ignored" is not what the
// code does: a revision at or below compactRev that is live at rev is hashed.
func TestReviewCompactRevNotIgnored(t *testing.T) {
	mk := func(v string) *store {
		s, _ := newRStore(t)
		s.Put([]byte("foo"), []byte(v), lease.NoLease)   // 2
		s.Put([]byte("bar"), []byte("x"), lease.NoLease) // 3
		return s
	}
	a, b := mk("a"), mk("b")
	ha, _, _ := a.HashStorage().HashByRevWithCompactRev(3, 2)
	hb, _, _ := b.HashStorage().HashByRevWithCompactRev(3, 2)
	t.Logf("stores differing only at revision 2, --rev 3 --compact-rev 2: %+v vs %+v", ha, hb)
	if ha.Hash != hb.Hash {
		t.Errorf("revision 2 (<= compactRev 2) is not ignored: hashes differ (%d vs %d); it is hashed because it is live at 3", ha.Hash, hb.Hash)
	}
	// And with nothing live at rev (empty keep), no revision below compactRev is ignored.
	mk2 := func(v string) *store {
		s, _ := newRStore(t)
		s.Put([]byte("foo"), []byte(v), lease.NoLease) // 2
		s.DeleteRange([]byte("foo"), nil)              // 3
		s.Put([]byte("bar"), []byte("x"), lease.NoLease) // 4
		s.DeleteRange([]byte("bar"), nil)              // 5
		return s
	}
	c, d := mk2("a"), mk2("b")
	hc, _, _ := c.HashStorage().HashByRevWithCompactRev(5, 4)
	hd, _, _ := d.HashStorage().HashByRevWithCompactRev(5, 4)
	t.Logf("empty keep, stores differing only at revision 2, --rev 5 --compact-rev 4: %+v vs %+v", hc, hd)
	if hc.Hash != hd.Hash {
		t.Errorf("empty keep: revision 2 (<= compactRev 4, deleted at 3) is hashed: %d vs %d", hc.Hash, hd.Hash)
	}
}

// R4: the detailed entries carry no sub-revision and no tombstone mark: a delete and a
// put of the same key in one transaction give two entries with the same key and
// modRevision.
func TestReviewDetailedTombstoneAmbiguous(t *testing.T) {
	s, _ := newRStore(t)
	s.Put([]byte("foo"), []byte("v2"), lease.NoLease) // 2
	txn := s.Write(traceutil.TODO())
	txn.DeleteRange([]byte("foo"), nil)              // 3.0 tombstone
	txn.Put([]byte("foo"), []byte("v3"), lease.NoLease) // 3.1
	txn.End()
	d, _, err := s.HashStorage().HashByRevDetailed(0, 0)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("key hashes: %+v (KeyCount %d)", d.KeyHashes, d.KeyCount)
	seen := map[string]int{}
	for _, k := range d.KeyHashes {
		seen[fmt.Sprintf("%s@%d", k.Key, k.ModRev)]++
	}
	for k, n := range seen {
		if n > 1 {
			t.Errorf("%d entries share key@modRevision %s (tombstone and put not distinguished)", n, k)
		}
	}
}

type errReader struct{}

func (errReader) UnsafeRange(backend.Bucket, []byte, []byte, int64) ([][]byte, [][]byte) {
	return nil, nil
}
func (errReader) UnsafeForEach(backend.Bucket, func(k, v []byte) error) error {
	return errors.New("forEach failed")
}

// R5: on an UnsafeForEach error unsafeHashByRev still returns the hasher's
// revision fields, unsafeHashByRevDetailed returns a zero result.
func TestReviewUnsafeHashErrorFields(t *testing.T) {
	h, err := unsafeHashByRev(errReader{}, 7, 9, nil)
	d, derr := unsafeHashByRevDetailed(errReader{}, 7, 9, nil)
	t.Logf("unsafeHashByRev: %+v err=%v", h, err)
	t.Logf("unsafeHashByRevDetailed: %+v err=%v", d, derr)
	if d.CompactRevision != 7 || d.TotalHash.CompactRevision != 7 || d.Revision != 9 {
		t.Errorf("detailed result on error has CompactRevision %d / TotalHash %+v / Revision %d, not 7/9", d.CompactRevision, d.TotalHash, d.Revision)
	}
}

// R6: the hash cache returns a hash the compaction job stored for (rev, compactRev)
// to a caller passing that compactRev, and (unchanged) any cached hash at rev for
// compactRev <= 0; a different positive compactRev recomputes.
func TestReviewHashCache(t *testing.T) {
	s, _ := newRStore(t)
	for i := 2; i <= 6; i++ {
		s.Put([]byte("foo"), []byte(fmt.Sprintf("v%d", i)), lease.NoLease)
	}
	hs := s.HashStorage()
	hs.Store(KeyValueHash{Hash: 42, CompactRevision: 3, Revision: 5})
	a, _, _ := hs.HashByRevWithCompactRev(5, 0)
	b, _, _ := hs.HashByRevWithCompactRev(5, 3)
	c, _, _ := hs.HashByRevWithCompactRev(5, 4)
	t.Logf("cached(5,0)=%+v cached(5,3)=%+v computed(5,4)=%+v", a, b, c)
	if a.Hash != 42 || b.Hash != 42 || c.Hash == 42 {
		t.Errorf("unexpected cache behavior")
	}
}
