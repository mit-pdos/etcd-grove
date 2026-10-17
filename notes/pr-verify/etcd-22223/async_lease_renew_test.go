// Review test for etcd-io/etcd#22223: with async storage writes, a lease
// granted through a follower is not found by the leader's LeaseRenew when the
// leader's own WAL append is slower than the followers'.
package integration

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestReviewAsyncLeaseRenewViaFollowerAfterGrant(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	follower := (lead + 1) % 3
	lc := integration.ToGRPC(clus.Client(follower)).Lease
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	lac, err := lc.LeaseKeepAlive(ctx)
	require.NoError(t, err)
	zero := 0
	for i := 0; i < 20; i++ {
		resp, err := lc.LeaseGrant(ctx, &pb.LeaseGrantRequest{TTL: 60})
		require.NoError(t, err)
		require.NoError(t, lac.Send(&pb.LeaseKeepAliveRequest{ID: resp.ID}))
		rresp, err := lac.Recv()
		require.NoError(t, err)
		if rresp.TTL == 0 {
			zero++
		}
	}
	if zero > 0 {
		t.Fatalf("%d of 20 keepalives right after a successful LeaseGrant (through follower m%d) returned TTL 0 (lease not found on the leader)", zero, follower)
	}
}
