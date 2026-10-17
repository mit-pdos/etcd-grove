package mvcc

import (
	"testing"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Review of etcd-io/etcd#22377: the hashes members compare (the compaction
// hash of each compaction, HashByRev) over a history with the affected shape,
// printed so that the base and the PR can be compared.
func TestReviewHashesRecreate(t *testing.T) {
	lg := zaptest.NewLogger(t, zaptest.WrapOptions(zap.WithFatalHook(zapcore.WriteThenPanic)), zaptest.Level(zapcore.WarnLevel))
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(lg, b, &lease.FakeLessor{}, StoreConfig{})
	defer func() { s.Close(); b.Close() }()

	s.Put([]byte("foo"), []byte("v1"), lease.NoLease) // 2
	tw := s.Write(traceutil.TODO())                    // 3: delete and put again
	tw.DeleteRange([]byte("foo"), nil)
	tw.Put([]byte("foo"), []byte("v2"), lease.NoLease)
	tw.End()
	s.Put([]byte("bar"), []byte("b"), lease.NoLease) // 4
	s.Put([]byte("baz"), []byte("b"), lease.NoLease) // 5

	for _, c := range []int64{3, 5} {
		ch, err := s.Compact(traceutil.TODO(), c)
		if err != nil {
			t.Fatal(err)
		}
		<-ch
		hs := s.HashStorage().Hashes()
		last := hs[len(hs)-1]
		t.Logf("compaction at %d: compaction hash %d (compactRev %d, prev %d)", c, last.Hash, last.CompactRevision, last.Revision)
		h, cur, err := s.HashStorage().HashByRev(0)
		t.Logf("after compaction at %d: HashByRev(cur=%d) = %d (compactRev %d), err %v", c, cur, h.Hash, h.CompactRevision, err)
	}
	tr := s.Read(ConcurrentReadTxMode, traceutil.TODO())
	r, err := tr.Range(t.Context(), []byte("foo"), nil, RangeOptions{})
	tr.End()
	t.Logf("range foo: %v %v", r, err)
}
