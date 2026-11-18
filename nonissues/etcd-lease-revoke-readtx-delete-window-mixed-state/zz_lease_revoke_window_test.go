package mvcc

// A read transaction can see a lease revoke half applied: lessor.Revoke deletes the lease's keys
// (mvcc tombstones, puts in the Key bucket) and its record in the Lease bucket (a delete) in one
// batch, whose Unlock writes the tombstones back into the read buffer and releases readTx's lock
// before it commits the record's delete (batchTxBuffered.Unlock, batch_tx.go:328-357). A read in
// between sees the key deleted by the revoke and the lease's record still there.

import (
	"encoding/binary"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func TestLeaseRevokeReadWindowMixedState(t *testing.T) {
	lg := zap.NewNop()
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	le := lease.NewLessor(lg, be, nil, lease.LessorConfig{MinLeaseTTL: 1000})
	defer le.Stop()
	s := NewStore(lg, be, le, StoreConfig{})
	defer s.Close()

	type step struct {
		id  lease.LeaseID
		rev int64 // the revision of the revoke's tombstone
	}
	var cur atomic.Pointer[step]
	var mixed, reads atomic.Int64
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
				st := cur.Load()
				if st == nil {
					continue
				}
				lkey := make([]byte, 8)
				binary.BigEndian.PutUint64(lkey, uint64(st.id))
				start := RevToBytes(Revision{Main: st.rev}, NewRevBytes())
				end := RevToBytes(Revision{Main: st.rev + 1}, NewRevBytes())
				tx := be.ReadTx()
				tx.RLock()
				lk, _ := tx.UnsafeRange(schema.Lease, lkey, nil, 0)
				kk, _ := tx.UnsafeRange(schema.Key, start, end, 0)
				tx.RUnlock()
				reads.Add(1)
				// recorded states: before the revoke, the record and no tombstone at st.rev;
				// after it, the tombstone and no record
				if len(lk) > 0 && len(kk) > 0 && isTombstone(kk[0]) {
					mixed.Add(1)
				}
			}
		}()
	}
	deadline := time.Now().Add(60 * time.Second)
	for i := 1; i < 20000 && time.Now().Before(deadline) && mixed.Load() == 0; i++ {
		id := lease.LeaseID(i)
		if _, err := le.Grant(id, 1000); err != nil {
			t.Fatal(err)
		}
		s.Put([]byte("k"), []byte("v"), id)
		cur.Store(&step{id: id, rev: s.Rev() + 1})
		if err := le.Revoke(id); err != nil {
			t.Fatal(err)
		}
	}
	close(stop)
	wg.Wait()
	t.Logf("reads %d, reads of an unrecorded state %d", reads.Load(), mixed.Load())
	if mixed.Load() > 0 {
		t.Errorf("a read transaction saw a revoked lease's key deleted and its record still present")
	}
}
