package mvcc

import (
	"errors"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func waitCh(t *testing.T, ch <-chan struct{}) {
	t.Helper()
	select {
	case <-ch:
	case <-time.After(10 * time.Second):
		t.Fatal("channel did not close")
	}
}

// Fresh store: head is 1, compactMainRev -1.
func TestProbeCompactFreshStore(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer b.Close()
	defer s.Close()
	for _, r := range []int64{-1, -5} {
		if _, err := s.Compact(traceutil.TODO(), r); !errors.Is(err, ErrCompacted) {
			t.Fatalf("Compact(%d) fresh = %v", r, err)
		}
	}
	if _, err := s.Compact(traceutil.TODO(), 0); err != nil {
		t.Fatalf("Compact(0) = %v", err)
	}
	if _, err := s.Compact(traceutil.TODO(), 0); !errors.Is(err, ErrCompacted) {
		t.Fatalf("Compact(0) again (head 1) = %v, want ErrCompacted", err)
	}
	ch, err := s.Compact(traceutil.TODO(), 1)
	if err != nil {
		t.Fatalf("Compact(1) = %v", err)
	}
	waitCh(t, ch)
	ch, err = s.Compact(traceutil.TODO(), 1)
	if err != nil {
		t.Fatalf("Compact(1) again at head = %v, want nil", err)
	}
	waitCh(t, ch)
}

// The no-op's barrier channel closes only after the earlier compaction job: a
// "physical" caller waiting on it sees the compaction at rev finished.
func TestProbeNoopBarrierAfterJob(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{CompactionBatchLimit: 1, CompactionSleepInterval: 50 * time.Millisecond})
	defer b.Close()
	defer s.Close()
	for i := 0; i < 20; i++ {
		s.Put([]byte{byte('a' + i)}, []byte("v"), lease.NoLease)
		s.Put([]byte{byte('a' + i)}, []byte("w"), lease.NoLease)
	}
	head := s.Rev()
	if _, err := s.Compact(traceutil.TODO(), head); err != nil { // do not wait
		t.Fatal(err)
	}
	ch, err := s.Compact(traceutil.TODO(), head)
	if err != nil {
		t.Fatalf("no-op = %v", err)
	}
	waitCh(t, ch)
	tx := b.ReadTx()
	tx.RLock()
	fin, ok := UnsafeReadFinishedCompact(tx)
	tx.RUnlock()
	if !ok || fin != head {
		t.Fatalf("after the no-op's channel: finished compact = %d,%v, want %d", fin, ok, head)
	}
}

// Head revision is a tombstone: after compaction at it and reopen, currentRev is
// restored from compactMainRev; Compact(head) must still be a no-op.
func TestProbeTombstoneHeadReopen(t *testing.T) {
	b, tmpPath := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	s.DeleteRange([]byte("foo"), nil)
	head := s.Rev()
	ch, err := s.Compact(traceutil.TODO(), head)
	if err != nil {
		t.Fatal(err)
	}
	waitCh(t, ch)
	s.Close()
	b.Close()
	b = backend.NewDefaultBackend(zaptest.NewLogger(t), tmpPath)
	s = NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer b.Close()
	defer s.Close()
	if s.Rev() != head {
		t.Fatalf("Rev() after reopen = %d, want %d", s.Rev(), head)
	}
	ch, err = s.Compact(traceutil.TODO(), head)
	if err != nil {
		t.Fatalf("Compact(head=%d) after reopen = %v, want nil", head, err)
	}
	waitCh(t, ch)
}
