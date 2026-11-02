package mvcc

import (
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestRestoreDuringQueuedCompaction: a compaction is running (here a slow one:
// one key per batch, a long pause between batches), a second one is queued
// behind it, and the store is restored from a snapshot (a follower installing
// a snapshot). Restore interrupts the running compaction and closes its
// channel; the queued compaction's channel, which an etcdserver Compact
// request with Physical set waits on, should be closed too.
func TestRestoreDuringQueuedCompaction(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{
		CompactionBatchLimit:    1,
		CompactionSleepInterval: time.Hour,
	})
	t.Cleanup(func() { s.Close(); s.b.Close() })

	for i := 0; i < 5; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	}

	ch1, err := s.Compact(traceutil.TODO(), 2) // runs, then pauses after its first batch
	if err != nil {
		t.Fatal(err)
	}
	ch2, err := s.Compact(traceutil.TODO(), 3) // queued behind it
	if err != nil {
		t.Fatal(err)
	}
	time.Sleep(100 * time.Millisecond)

	nb, _ := betesting.NewDefaultTmpBackend(t)
	if err := s.Restore(nb); err != nil {
		t.Fatalf("Restore: %v", err)
	}

	for i, ch := range []<-chan struct{}{ch1, ch2} {
		select {
		case <-ch:
		case <-time.After(5 * time.Second):
			t.Errorf("the channel of compaction %d is not closed 5s after Restore", i+1)
		}
	}
}
