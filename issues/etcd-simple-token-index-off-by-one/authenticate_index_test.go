// Reproduction of issues/etcd-simple-token-index-off-by-one.md (etcd-io/etcd#18437).
//
// Package apply, file server/etcdserver/apply/authenticate_index_test.go of go.etcd.io/etcd
// (module go.etcd.io/etcd/server/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch
// goose-lean of upamanyus/etcd). It uses the package's test helpers of auth_test.go
// (fakeRaftStatusGetter, fakeSnapshotServer, mustCreateRolesAndEnableAuth).
//
// Run, in server/:
//
//	GOTOOLCHAIN=go1.27.1 go test ./etcdserver/apply -run '^TestSimpleTokenNamesPreviousIndex$' -count=1
//
// Passes at the pin, which shows the bug: the token issued by the entry at index 10 names
// index 9, and member B, having applied 9 but not 10, rejects it at once with
// ErrInvalidAuthToken instead of waiting.
//
// The simple token names the index the token-issuing Authenticate entry was applied at, and a
// member that receives the token waits (indexWaiter = applyWait.Wait) for that index before it
// looks the token up. applierV3backend.Authenticate takes the index from ConsistentIndex(), which
// while an entry is applied is still the previous entry's index (applyEntries sets only the
// *applying* index before applyEntryNormal; the stored one moves in the post-lock hook or after
// the entry). So the token names entry-1, and a member that has applied entry-1 but not the
// Authenticate entry rejects the fresh token with ErrInvalidAuthToken instead of waiting.
package apply

import (
	"context"
	"errors"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// member builds an auth applier whose token provider's waiter reports index i as applied iff
// i <= *applied.
func member(t *testing.T, applied *uint64) (*authApplierV3, cindex.ConsistentIndexer, auth.AuthStore) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, be) })
	cluster := membership.NewCluster(lg)
	lessor := lease.NewLessor(lg, be, cluster, lease.LessorConfig{})
	kv := mvcc.NewStore(lg, be, lessor, mvcc.StoreConfig{})
	alarmStore, err := v3alarm.NewAlarmStore(lg, schema.NewAlarmBackend(lg, be))
	require.NoError(t, err)
	waiter := func(i uint64) <-chan struct{} {
		ch := make(chan struct{})
		if i <= *applied {
			close(ch)
		}
		return ch
	}
	tp, err := auth.NewTokenProvider(lg, "simple", waiter, 300*time.Second)
	require.NoError(t, err)
	as := auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), tp, bcrypt.MinCost)
	ci := cindex.NewConsistentIndex(be)
	aa := newAuthApplierV3(as, newApplierV3Backend(ApplierOptions{
		Logger: lg, KV: kv, AlarmStore: alarmStore, ConsistentIndex: ci, AuthStore: as,
		Lessor: lessor, Cluster: cluster, RaftStatus: &fakeRaftStatusGetter{},
		SnapshotServer: &fakeSnapshotServer{},
	}), lessor)
	mustCreateRolesAndEnableAuth(t, aa)
	_, err = aa.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Password: "pw"})
	require.NoError(t, err)
	return aa, ci, as
}

func TestSimpleTokenNamesPreviousIndex(t *testing.T) {
	var appliedA, appliedB uint64
	a, ciA, _ := member(t, &appliedA)
	_, _, asB := member(t, &appliedB)

	// Member A applies the Authenticate entry at index 10, as EtcdServer.applyEntries does:
	// entries up to 9 applied, the applying index set to 10.
	ciA.SetConsistentIndex(9, 1)
	ciA.SetConsistentApplyingIndex(10, 1)
	resp, err := a.Authenticate(&pb.InternalAuthenticateRequest{Name: "alice", SimpleToken: "prefix"})
	require.NoError(t, err)
	appliedA = 10
	t.Logf("token issued by the entry at index 10: %q", resp.Token)
	require.Truef(t, strings.HasSuffix(resp.Token, ".9"), "token %q does not name index 9", resp.Token)

	// Member B has applied index 9 but not yet the Authenticate entry at 10.
	appliedB = 9
	md := metadata.New(map[string]string{rpctypes.TokenFieldNameGRPC: resp.Token})
	ctx, cancel := context.WithTimeout(metadata.NewIncomingContext(context.Background(), md), 2*time.Second)
	defer cancel()
	start := time.Now()
	_, err = asB.AuthInfoFromCtx(ctx)
	t.Logf("member B: err=%v after %v", err, time.Since(start))
	require.Truef(t, errors.Is(err, auth.ErrInvalidAuthToken), "got %v", err)
	require.Less(t, time.Since(start), time.Second, "member B did not wait for the Authenticate entry")
}
