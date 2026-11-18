package schema

// A read of the membership buckets can see a member removal half applied: MustDeleteMemberFromBackend
// deletes members/<id> and puts members_removed/<id> in one batch, whose Unlock writes the put back
// into the read buffer and releases readTx's lock before it commits the delete
// (batchTxBuffered.Unlock, batch_tx.go:328-357). A MustReadMembersFromBackend in between returns
// the member both as a member and as removed, a state no step recorded.

import (
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func TestMembershipReadWindowMixedState(t *testing.T) {
	lg := zap.NewNop()
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	mb := NewMembershipBackend(lg, be)
	mb.MustCreateBackendBuckets()

	// The recorded states: after MustSaveMemberToBackend(m) m is a member and not removed; after
	// MustDeleteMemberFromBackend(m.ID) it is removed and not a member. Never both.
	var mixed, reads atomic.Int64
	var firstID atomic.Uint64
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
				members, removed := mb.MustReadMembersFromBackend()
				reads.Add(1)
				for id := range members {
					if removed[id] {
						if mixed.Add(1) == 1 {
							firstID.Store(uint64(id))
						}
					}
				}
			}
		}()
	}
	deadline := time.Now().Add(60 * time.Second)
	for i := 1; i < 20000 && time.Now().Before(deadline) && mixed.Load() == 0; i++ {
		m := membership.NewMember("m", types.MustNewURLs([]string{"http://127.0.0.1:2380"}), "c", nil)
		m.ID = types.ID(i)
		mb.MustSaveMemberToBackend(m)
		mb.MustDeleteMemberFromBackend(m.ID)
	}
	close(stop)
	wg.Wait()
	t.Logf("reads %d, reads of an unrecorded state %d (first member %x)", reads.Load(), mixed.Load(),
		firstID.Load())
	if mixed.Load() > 0 {
		t.Errorf("MustReadMembersFromBackend saw member %x both in members and in members_removed",
			firstID.Load())
	}
}
