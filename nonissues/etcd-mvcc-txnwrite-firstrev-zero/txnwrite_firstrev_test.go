// Copy into server/storage/mvcc of etcd-io/etcd.

package mvcc

import (
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestTxnWriteFirstRev: ReadView.FirstRev is documented as "the first KV
// revision at the time of opening the txn. After a compaction, the first
// revision increases to the compaction revision." A read txn returns the
// compaction revision; a write txn returns 0.
func TestTxnWriteFirstRev(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	for i := 0; i < 5; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease) // revisions 2..6
	}
	done, err := s.Compact(traceutil.TODO(), 4)
	if err != nil {
		t.Fatal(err)
	}
	<-done

	r := s.Read(ConcurrentReadTxMode, traceutil.TODO())
	readFirst := r.FirstRev()
	r.End()
	w := s.Write(traceutil.TODO())
	writeFirst := w.FirstRev()
	w.End()

	if readFirst != 4 {
		t.Fatalf("Read().FirstRev() = %d, want the compaction revision 4", readFirst)
	}
	if writeFirst != readFirst {
		t.Fatalf("Write().FirstRev() = %d, Read().FirstRev() = %d: want both the compaction revision 4", writeFirst, readFirst)
	}
}
