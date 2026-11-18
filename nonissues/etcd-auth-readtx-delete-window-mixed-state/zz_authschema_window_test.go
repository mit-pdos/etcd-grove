package schema

// A read transaction of the auth buckets can see a state no admin step recorded: an auth batch that
// deletes a key and puts another (UserDelete: the user's delete and the revision's put) writes its
// puts back into the read buffer and releases readTx's lock before it commits the delete
// (batchTxBuffered.Unlock, batch_tx.go:328-357), so a reader in between sees the new revision and
// the deleted user (still in bbolt's committed snapshot). etcd-grove's trusted contract
// authReadTxOk (authSchemaSrv) promises every RLock a recorded state.

import (
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"
	"golang.org/x/crypto/bcrypt"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/auth"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func TestAuthSchemaReadWindowMixedState(t *testing.T) {
	lg := zap.NewNop()
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)
	abe := NewAuthBackend(lg, be)
	tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} {
		ch := make(chan struct{})
		close(ch)
		return ch
	}, 300*time.Second)
	if err != nil {
		t.Fatal(err)
	}
	as := auth.NewAuthStore(lg, abe, tp, bcrypt.MinCost)
	defer as.Close()

	// The recorded states: revision 1, no user (NewAuthStore); each UserAdd records an even
	// revision with the user, each UserDelete an odd one without it.
	var mixed, reads atomic.Int64
	var firstRev atomic.Uint64
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
				// as authStore.CheckPassword's closure (store.go:373-387): one read transaction
				tx := abe.ReadTx()
				tx.RLock()
				u := tx.UnsafeGetUser("u")
				rev := tx.UnsafeReadAuthRevision()
				tx.RUnlock()
				reads.Add(1)
				if (u != nil) != (rev%2 == 0) {
					if mixed.Add(1) == 1 {
						firstRev.Store(rev)
					}
				}
			}
		}()
	}
	deadline := time.Now().Add(60 * time.Second)
	for i := 0; i < 200000 && time.Now().Before(deadline) && mixed.Load() == 0; i++ {
		if _, err := as.UserAdd(&pb.AuthUserAddRequest{Name: "u",
			Options: &authpb.UserAddOptions{NoPassword: true}}); err != nil {
			t.Fatal(err)
		}
		if _, err := as.UserDelete(&pb.AuthUserDeleteRequest{Name: "u"}); err != nil {
			t.Fatal(err)
		}
	}
	close(stop)
	wg.Wait()
	t.Logf("reads %d, reads of an unrecorded state %d (first at revision %d)", reads.Load(),
		mixed.Load(), firstRev.Load())
	if mixed.Load() > 0 {
		t.Errorf("a read transaction saw an unrecorded auth state: user present at the odd "+
			"revision %d (written by UserDelete, which deleted it)", firstRev.Load())
	}
}
