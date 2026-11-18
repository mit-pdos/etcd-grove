package mvcc

// A read transaction can see a compaction's last batch half applied: scheduleCompaction deletes the
// compacted revisions from the Key bucket and puts finishedCompactRev in Meta in one batch, whose
// Unlock writes the put back into the read buffer and releases readTx's lock before it commits the
// deletes (batchTxBuffered.Unlock, batch_tx.go:328-357). A read in between sees the compaction
// finished at c and a revision it deleted (below c, not kept) still in the Key bucket.

import (
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func TestCompactionReadWindowMixedState(t *testing.T) {
	lg := zap.NewNop()
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	s := NewStore(lg, be, &lease.FakeLessor{}, StoreConfig{})
	defer s.Close()

	var mixed, reads atomic.Int64
	var firstFin atomic.Int64
	stop := make(chan struct{})
	var wg sync.WaitGroup
	for r := 0; r < 4; r++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				tx := be.ReadTx()
				tx.RLock()
				fin, ok := UnsafeReadFinishedCompact(tx)
				var kk [][]byte
				if ok && fin > 2 {
					kk, _ = tx.UnsafeRange(schema.Key, RevToBytes(Revision{Main: fin - 1}, NewRevBytes()),
						RevToBytes(Revision{Main: fin}, NewRevBytes()), 0)
				}
				tx.RUnlock()
				reads.Add(1)
				// every revision is a put of the one key "k": a compaction at fin keeps only fin
				// of the revisions up to fin, so a recorded state with finishedCompactRev = fin
				// has no revision fin-1
				if len(kk) > 0 {
					if mixed.Add(1) == 1 {
						firstFin.Store(fin)
					}
				}
			}
		}()
	}
	deadline := time.Now().Add(60 * time.Second)
	for i := 0; i < 20000 && time.Now().Before(deadline) && mixed.Load() == 0; i++ {
		s.Put([]byte("k"), []byte("v"), lease.NoLease)
		s.Put([]byte("k"), []byte("v"), lease.NoLease)
		done, err := s.Compact(traceutil.TODO(), s.Rev())
		if err != nil {
			t.Fatal(err)
		}
		<-done
	}
	close(stop)
	wg.Wait()
	t.Logf("reads %d, reads of an unrecorded state %d (first at finishedCompactRev %d)", reads.Load(),
		mixed.Load(), firstFin.Load())
	if mixed.Load() > 0 {
		t.Errorf("a read transaction saw finishedCompactRev %d and the compacted revision %d",
			firstFin.Load(), firstFin.Load()-1)
	}
}
