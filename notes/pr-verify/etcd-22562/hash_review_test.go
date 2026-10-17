// Reviewer's randomized check for etcd-io/etcd#22562 (not for upstream):
// two compactions queued (c0 then c1), HashKV at every stage of their progress
// (nothing deleted, a random part of c0's deletions, c0 done, c1 done, after a
// restart), and the stored hash of c1 against HashKV(c1) computed while c0 is
// the compaction revision.
package mvcc

import (
	"fmt"
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func reviewOps(s *store, rnd *rand.Rand, n int, delPut bool) {
	keys := []string{"a", "b", "c"}
	for i := 0; i < n; i++ {
		k := []byte(keys[rnd.Intn(len(keys))])
		switch x := rnd.Intn(10); {
		case delPut && x == 0:
			txn := s.Write(traceutil.TODO())
			txn.DeleteRange(k, nil)
			txn.Put(k, []byte(fmt.Sprint(i)), lease.NoLease)
			txn.End()
		case x < 4:
			s.DeleteRange(k, nil)
		default:
			s.Put(k, []byte(fmt.Sprint(i)), lease.NoLease)
		}
	}
}

// deletePartOf deletes from the Key bucket a random part of what compaction at
// rev with kept set keep deletes (a compaction in progress; any subset, as
// HashKV under the read lock could only see a prefix, but the filter should not
// care).
func deletePartOf(s *store, rnd *rand.Rand, rev int64, keep map[Revision]struct{}) {
	deletePart(s, rnd, rev, keep, false)
}

// deletePrefixOf deletes a prefix (in revision order) of what compaction at
// rev deletes: what a crash in the middle of scheduleCompaction leaves (its
// batches delete in key order and commit one by one).
func deletePrefixOf(s *store, rnd *rand.Rand, rev int64, keep map[Revision]struct{}) {
	deletePart(s, rnd, rev, keep, true)
}

func deletePart(s *store, rnd *rand.Rand, rev int64, keep map[Revision]struct{}, prefix bool) {
	stop := rnd.Int63n(rev + 2)
	tx := s.b.BatchTx()
	tx.LockOutsideApply()
	min := RevToBytes(Revision{Main: 0}, NewRevBytes())
	max := RevToBytes(Revision{Main: rev + 1}, NewRevBytes())
	keys, _ := tx.UnsafeRange(schema.Key, min, max, 0)
	for _, k := range keys {
		r := BytesToRev(k)
		if prefix && r.Main >= stop {
			break
		}
		if _, ok := keep[r]; !ok && (prefix || rnd.Intn(2) == 0) {
			tx.UnsafeDelete(schema.Key, k)
		}
	}
	tx.Unlock()
	s.b.ForceCommit()
}

func TestReviewHashProgressAndRestart(t *testing.T) {
	for _, delPut := range []bool{false, true} {
		fails := 0
		for seed := int64(0); seed < 3000; seed++ {
			if err := reviewTrial(t, seed, delPut); err != nil {
				fails++
				if fails <= 3 {
					t.Logf("delPut=%v seed %d: %v", delPut, seed, err)
				}
			}
		}
		t.Logf("delPut=%v: %d of 3000 trials fail", delPut, fails)
		if !delPut && fails > 0 {
			t.Errorf("failures without delete-then-put")
		}
	}
}

func reviewTrial(t *testing.T, seed int64, delPut bool) (err error) {
	rnd := rand.New(rand.NewSource(seed))
	b, _ := betesting.NewDefaultTmpBackend(t)
	lg := zaptest.NewLogger(t).WithOptions()
	s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
	defer func() {
		if p := recover(); p != nil {
			err = fmt.Errorf("panic: %v", p)
		}
		cleanup(s, b)
	}()
	reviewOps(s, rnd, 1+rnd.Intn(12), delPut)
	if s.Rev() < 3 {
		return nil
	}
	c0 := 1 + rnd.Int63n(s.Rev()-1)
	c1 := c0 + 1 + rnd.Int63n(s.Rev()-c0)
	if c1 > s.Rev() {
		return nil
	}
	// compaction at c0 scheduled; its job has compacted the index only.
	_, prev0, e := s.updateCompactRev(c0)
	require.NoError(t, e)
	keep0 := s.kvindex.Compact(c0)
	// CompactHashCheck: a member at compaction revision c0 answers HashKV(c1).
	hX, _, e := s.hashByRev(c1)
	require.NoError(t, e)
	deletePartOf(s, rnd, c0, keep0)
	hX2, _, e := s.hashByRev(c1)
	require.NoError(t, e)
	if hX != hX2 {
		return fmt.Errorf("HashKV(c1=%d) at c0=%d changed during compaction c0: %x vs %x", c1, c0, hX.Hash, hX2.Hash)
	}
	_, prev1, e := s.updateCompactRev(c1)
	require.NoError(t, e)
	require.Equal(t, c0, prev1)
	reviewOps(s, rnd, rnd.Intn(4), delPut)
	hA, _, e := s.hashByRev(0)
	require.NoError(t, e)
	_, e = s.scheduleCompaction(c0, prev0)
	require.NoError(t, e)
	hB, _, e := s.hashByRev(0)
	require.NoError(t, e)
	if hA != hB {
		return fmt.Errorf("HashKV during c0 (c0=%d c1=%d) %x, after c0 %x", c0, c1, hA.Hash, hB.Hash)
	}
	stored, e := s.scheduleCompaction(c1, prev1)
	require.NoError(t, e)
	if stored != hX {
		return fmt.Errorf("stored hash of c1=%d (%+v) != HashKV(c1) at c0 (%+v)", c1, stored, hX)
	}
	hC, _, e := s.hashByRev(0)
	require.NoError(t, e)
	if hA != hC {
		return fmt.Errorf("HashKV during c0 (c0=%d c1=%d) %x, after c1 %x", c0, c1, hA.Hash, hC.Hash)
	}
	// restart (index rebuilt from the compacted bucket)
	s.Close()
	s = NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
	hD, _, e := s.hashByRev(hC.Revision)
	require.NoError(t, e)
	if hC != hD {
		return fmt.Errorf("HashKV after restart %+v, before %+v", hD, hC)
	}
	return nil
}

// A compaction at cp finished, one at c0 scheduled and partly done, then a
// restart (the index rebuilt from the partly compacted bucket, the compaction
// resumed): HashKV must be the same before the restart, right after it, and
// after the resumed compaction.
func TestReviewHashRestartMidCompaction(t *testing.T) {
	fails := 0
	for seed := int64(0); seed < 3000; seed++ {
		if err := reviewRestartTrial(t, seed); err != nil {
			fails++
			if fails <= 3 {
				t.Logf("seed %d: %v", seed, err)
			}
		}
	}
	t.Logf("%d of 3000 trials fail", fails)
	if fails > 0 {
		t.Errorf("failures")
	}
}

var reviewDebug func(s *store, tag string, c0, rev int64)

func reviewRestartTrial(t *testing.T, seed int64) (err error) {
	rnd := rand.New(rand.NewSource(seed))
	b, _ := betesting.NewDefaultTmpBackend(t)
	lg := zaptest.NewLogger(t)
	s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
	defer func() {
		if p := recover(); p != nil {
			err = fmt.Errorf("panic: %v", p)
		}
		cleanup(s, b)
	}()
	reviewOps(s, rnd, 1+rnd.Intn(8), false)
	if s.Rev() >= 2 && rnd.Intn(2) == 0 {
		cp := 1 + rnd.Int63n(s.Rev())
		ch, e := s.Compact(traceutil.TODO(), cp)
		require.NoError(t, e)
		<-ch
	}
	reviewOps(s, rnd, 1+rnd.Intn(8), false)
	lo := s.compactMainRev
	if s.Rev() <= lo || s.Rev() < 2 {
		return nil
	}
	c0 := lo + 1 + rnd.Int63n(s.Rev()-lo)
	if c0 < 1 {
		c0 = 1
	}
	_, _, e := s.updateCompactRev(c0)
	require.NoError(t, e)
	keep0 := s.kvindex.Compact(c0)
	reviewOps(s, rnd, rnd.Intn(4), false)
	hX, _, e := s.hashByRev(0)
	require.NoError(t, e)
	if reviewDebug != nil {
		reviewDebug(s, "before partial", c0, hX.Revision)
	}
	deletePrefixOf(s, rnd, c0, keep0)
	if reviewDebug != nil {
		reviewDebug(s, "after partial", c0, hX.Revision)
	}
	s.Close()
	s = NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
	if reviewDebug != nil {
		reviewDebug(s, "after restart", c0, hX.Revision)
	}
	hY, _, e := s.hashByRev(hX.Revision)
	require.NoError(t, e)
	s.fifoSched.WaitFinish(1)
	hZ, _, e := s.hashByRev(hX.Revision)
	require.NoError(t, e)
	if hX != hY || hX != hZ {
		return fmt.Errorf("before restart %+v, right after %+v, after resumed compaction %+v", hX, hY, hZ)
	}
	return nil
}
