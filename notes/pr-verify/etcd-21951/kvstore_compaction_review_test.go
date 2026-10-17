package mvcc

import (
	"context"
	"sync/atomic"
	"testing"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

type lockCountingBackend struct {
	backend.Backend
	n atomic.Int32
}

func (b *lockCountingBackend) LockForSafeRangeDelete() {
	b.n.Add(1)
	b.Backend.LockForSafeRangeDelete()
}

// The range-scan compaction holds LockForSafeRangeDelete (excluding a concurrent
// non-blocking Defrag); the index-driven one deletes the same keys without it.
func TestReviewIndexDrivenSkipsSafeRangeDeleteLock(t *testing.T) {
	for _, indexDriven := range []bool{false, true} {
		raw, _ := betesting.NewDefaultTmpBackend(t)
		b := &lockCountingBackend{Backend: raw}
		s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{IndexDrivenCompaction: indexDriven})
		s.Put([]byte("foo"), []byte("v1"), lease.NoLease)
		s.Put([]byte("foo"), []byte("v2"), lease.NoLease)
		ch, err := s.Compact(traceutil.TODO(), 3)
		if err != nil {
			t.Fatal(err)
		}
		<-ch
		t.Logf("IndexDrivenCompaction=%v: LockForSafeRangeDelete calls = %d", indexDriven, b.n.Load())
		if indexDriven && b.n.Load() == 0 {
			t.Errorf("index-driven compaction deleted keys without LockForSafeRangeDelete")
		}
		s.Close()
		raw.Close()
	}
}

// etcd-io/etcd#22376's shape: the two modes leave different backends; only the
// range-scan one loses the live value.
func TestReviewDeleteThenPutModes(t *testing.T) {
	for _, indexDriven := range []bool{false, true} {
		b, _ := betesting.NewDefaultTmpBackend(t)
		lg := zaptest.NewLogger(t, zaptest.WrapOptions(zap.WithFatalHook(zapcore.WriteThenPanic)))
		s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{IndexDrivenCompaction: indexDriven})
		s.Put([]byte("foo"), []byte("v1"), lease.NoLease) // rev 2
		txn := s.Write(traceutil.TODO())                  // rev 3: delete then put
		txn.DeleteRange([]byte("foo"), nil)
		txn.Put([]byte("foo"), []byte("v2"), lease.NoLease)
		txn.End()
		ch, err := s.Compact(traceutil.TODO(), 3)
		if err != nil {
			t.Fatal(err)
		}
		<-ch
		func() {
			defer func() {
				if p := recover(); p != nil {
					t.Logf("IndexDrivenCompaction=%v: read after compaction panicked: %v", indexDriven, p)
				}
			}()
			r, err := s.Range(context.TODO(), []byte("foo"), nil, RangeOptions{})
			t.Logf("IndexDrivenCompaction=%v: read after compaction: %v %v", indexDriven, r.KVs, err)
		}()
		s.Close()
		b.Close()
	}
}
