package mvcc

import (
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Lets mvcc's tests compile at the PR head (kvstore_test.go's fake lacks it).
func (b *fakeBatchTx) UnsafeDeleteForCompaction(bucket backend.Bucket, key []byte) {
	b.UnsafeDelete(bucket, key)
}

// hashMidAndAfter writes a workload, compacts at the current revision with a
// batch limit of 1 and a long sleep between batches, and returns.hashByRev(0)
// while the compaction is paused after its first batch, and the hash of a
// second store that ran the same compaction to the end.
func hashMidAndAfter(t *testing.T, liveKey bool) (mid, done KeyValueHash) {
	run := func(cfg StoreConfig, wait func(<-chan struct{})) KeyValueHash {
		b, _ := betesting.NewDefaultTmpBackend(t)
		s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, cfg)
		defer betesting.Close(t, b)
		defer s.Close()
		for i := 0; i < 4; i++ {
			s.Put([]byte("a"), []byte("v"), lease.NoLease)
		}
		if liveKey {
			s.Put([]byte("b"), []byte("v"), lease.NoLease)
		}
		s.DeleteRange([]byte("a"), nil)
		s.Put([]byte("c"), []byte("v"), lease.NoLease)
		s.DeleteRange([]byte("c"), nil)
		ch, err := s.Compact(traceutil.TODO(), s.Rev())
		if err != nil {
			t.Fatal(err)
		}
		wait(ch)
		h, _, err := s.hashByRev(0)
		if err != nil {
			t.Fatal(err)
		}
		return h
	}
	mid = run(StoreConfig{CompactionBatchLimit: 1, CompactionSleepInterval: time.Hour},
		func(<-chan struct{}) { time.Sleep(300 * time.Millisecond) })
	done = run(StoreConfig{CompactionBatchLimit: 1000, CompactionSleepInterval: time.Millisecond},
		func(ch <-chan struct{}) { <-ch })
	return mid, done
}

// TestReviewHashByRevDuringCompaction: HashByRev of a store whose compaction
// is in progress, against one whose compaction is done, at the same revision
// and compact revision. With a live key (kvindex.Keep(rev) non-empty) the
// hasher skips the not-yet-deleted revisions; with no live key, keep is empty
// and kvHasher.WriteKeyValue does not skip them ("don't skip if there isn't
// one"), so the two hashes differ.
func TestReviewHashByRevDuringCompaction(t *testing.T) {
	for _, live := range []bool{true, false} {
		mid, done := hashMidAndAfter(t, live)
		t.Logf("liveKey=%v: mid-compaction %+v, after %+v", live, mid, done)
		if mid != done {
			t.Errorf("liveKey=%v: HashByRev differs between an in-progress and a finished compaction at the same revisions", live)
		}
	}
}
