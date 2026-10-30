package mvcc

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/schedule"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// setupPendingCompaction makes a store with a few revisions, occupies its
// scheduler's worker with a job that blocks until release is closed or the
// scheduler's context is cancelled, then calls Compact, whose job is left
// pending behind it. It returns the store, the channel Compact returned and
// release.
func setupPendingCompaction(t *testing.T) (*store, <-chan struct{}, chan struct{}) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	t.Cleanup(func() { s.Close(); s.b.Close() })

	s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	s.Put([]byte("foo"), []byte("bar1"), lease.NoLease)
	s.Put([]byte("foo"), []byte("bar2"), lease.NoLease)

	started := make(chan struct{})
	release := make(chan struct{})
	s.fifoSched.Schedule(schedule.NewJob("test_blocker", func(ctx context.Context) {
		close(started)
		select {
		case <-release:
		case <-ctx.Done(): // returns exactly when Stop cancels the scheduler
		}
	}))
	<-started // the worker is now busy with the blocker

	ch, err := s.Compact(traceutil.TODO(), 2)
	if err != nil {
		t.Fatalf("Compact: %v", err)
	}
	if p := s.fifoSched.Pending(); p != 2 { // blocker (running) + compaction
		t.Fatalf("expected 2 pending jobs (blocker + compaction), got %d", p)
	}
	return s, ch, release
}

// Control: without Restore, the compaction runs after the blocker and closes ch.
func TestCompactPendingNoRestoreCloses(t *testing.T) {
	_, ch, release := setupPendingCompaction(t)
	close(release)
	select {
	case <-ch:
		t.Logf("control: compaction channel closed")
	case <-time.After(2 * time.Second):
		t.Fatalf("control: compaction channel not closed within 2s")
	}
}

// Restore while the compaction job is pending: Stop cancels the scheduler,
// the blocker returns, the compaction job runs with a cancelled context and
// calls compactBarrier, which sees the closed stopc and returns without
// closing ch.
func TestCompactPendingDuringRestoreNeverCloses(t *testing.T) {
	s, ch, _ := setupPendingCompaction(t)

	nb, _ := betesting.NewDefaultTmpBackend(t)
	restored := make(chan error)
	go func() { restored <- s.Restore(nb) }()
	select {
	case err := <-restored:
		if err != nil {
			t.Fatalf("Restore: %v", err)
		}
	case <-time.After(10 * time.Second):
		t.Fatalf("Restore did not return")
	}

	select {
	case <-ch:
		t.Logf("compaction channel closed after Restore (no bug)")
	case <-time.After(2 * time.Second):
		t.Errorf("BUG: compaction channel returned by Compact was never closed after Restore (waited 2s); a Physical compaction RPC waiting on it would hang forever")
	}
}
