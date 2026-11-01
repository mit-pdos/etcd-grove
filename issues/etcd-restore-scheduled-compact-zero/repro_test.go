package mvcc

import (
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestRestoreScheduledCompactZero: a member that applied Compact(0) has
// compactMainRev 0. A snapshot taken by a member whose compaction at 0 was
// scheduled (scheduledCompactRev = 0 persisted) but not finished
// (no finishedCompactRev) restores to compactMainRev -1: restore() reads an
// absent scheduled record as 0 and treats 0 as "none". The two members then
// answer a re-issued Compact(0) differently.
func TestRestoreScheduledCompactZero(t *testing.T) {
	lg := zaptest.NewLogger(t)

	// The follower: applies Put, Compact(0).
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
	s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	ch, err := s.Compact(traceutil.TODO(), 0)
	if err != nil {
		t.Fatalf("Compact(0): %v", err)
	}
	<-ch
	if s.compactMainRev != 0 {
		t.Fatalf("follower compactMainRev = %d, want 0", s.compactMainRev)
	}
	if _, err := s.Compact(traceutil.TODO(), 0); err != ErrCompacted {
		t.Fatalf("follower: re-issued Compact(0) = %v, want ErrCompacted", err)
	}

	// The leader's snapshot: the same log (Put, Compact(0)), its compaction
	// at 0 scheduled and persisted, not finished (taken mid-job, or the
	// leader crashed before the job's last batch).
	b2, _ := betesting.NewDefaultTmpBackend(t)
	s2 := NewStore(lg, b2, &lease.FakeLessor{}, StoreConfig{})
	s2.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	s2.Close()
	tx := b2.BatchTx()
	tx.LockOutsideApply()
	UnsafeSetScheduledCompact(tx, 0)
	tx.Unlock()
	b2.ForceCommit()

	// The follower installs it.
	if err := s.Restore(b2); err != nil {
		t.Fatalf("Restore: %v", err)
	}
	t.Cleanup(func() { s.Close(); b.Close(); b2.Close() })
	if s.compactMainRev != 0 {
		t.Errorf("after Restore: compactMainRev = %d, want 0 (the log's compaction revision)", s.compactMainRev)
	}
	if _, err := s.Compact(traceutil.TODO(), 0); err != ErrCompacted {
		t.Errorf("after Restore: re-issued Compact(0) = %v, want ErrCompacted (as on the member that applied it)", err)
	}
}
