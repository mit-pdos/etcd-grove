package integration

import (
	"context"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3AuthRangePermittedDuringSnapshotRestore ensures that a member with auth
// enabled answers permission checks while it restores a snapshot from the leader.
// It calls the follower's IsRangePermitted for root as a serializable Range does
// (EtcdServer.doSerialize, on the gRPC goroutine). Uses authSetupRoot from
// v3_auth_test.go (same package).
func TestV3AuthRangePermittedDuringSnapshotRestore(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, SnapshotCount: 10, SnapshotCatchUpEntries: 5})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	authSetupRoot(t, integration.ToGRPC(clus.Client(lead)).Auth)
	lc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(lead).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer lc.Close()

	follower := clus.Members[(lead+1)%3]
	others := []*integration.Member{clus.Members[lead], clus.Members[(lead+2)%3]}
	fc, err := integration.NewClient(t, clientv3.Config{Endpoints: follower.Client.Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer fc.Close()
	ai := &auth.AuthInfo{Username: "root", Revision: follower.Server.AuthStore().Revision()}

	// With SnapshotCatchUpEntries 5, the leader compacts these entries away, so the
	// follower can only catch up by applying the leader's snapshot.
	follower.InjectPartition(t, others...)
	for i := 0; i < 20; i++ {
		_, err = lc.Put(t.Context(), "foo", "bar")
		require.NoError(t, err)
	}

	ctx, cancel := context.WithCancel(t.Context())
	var wg sync.WaitGroup
	for range 4 {
		wg.Go(func() {
			for ctx.Err() == nil {
				if perr := follower.Server.AuthStore().IsRangePermitted(ai, []byte("foo"), nil); perr != nil {
					t.Error(perr)
					return
				}
			}
		})
	}
	follower.RecoverPartition(t, others...)
	_, err = fc.Get(t.Context(), "foo")
	cancel()
	wg.Wait()
	require.NoError(t, err)
}
