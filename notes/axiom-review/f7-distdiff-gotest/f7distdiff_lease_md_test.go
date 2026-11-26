// F7 dist-axiom-diff review (2026-11-26): with auth off, outgoing metadata on a lease call
// (`token`, `authorization`, `hasleader`, a garbage client-api-version) never changes a
// successful reply; it can only turn a call into an error.
package integration

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc/metadata"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestF7DistDiffLeaseMetadata(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)
	base, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()

	ctxs := map[string]context.Context{
		"none":          base,
		"token":         metadata.AppendToOutgoingContext(base, "token", "garbage"),
		"authorization": metadata.AppendToOutgoingContext(base, "authorization", "Bearer garbage"),
		"hasleader":     clientv3.WithRequireLeader(base),
		"apiversion":    metadata.AppendToOutgoingContext(base, "client-api-version", "\xff\xfe"),
		"other":         metadata.AppendToOutgoingContext(base, "x-anything", "y"),
	}
	for i := 0; i < 3; i++ {
		cli, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(i).Endpoints()})
		require.NoError(t, err)
		for name, cx := range ctxs {
			g, err := cli.Grant(cx, 600)
			require.NoError(t, err, "%d %s Grant", i, name)
			require.NotZero(t, g.ID)
			ls, err := cli.Leases(cx)
			require.NoError(t, err, "%d %s Leases", i, name)
			seen := map[clientv3.LeaseID]bool{}
			found := false
			for _, l := range ls.Leases {
				require.False(t, seen[l.ID], "dup id")
				seen[l.ID] = true
				found = found || l.ID == g.ID
			}
			require.True(t, found, "%d %s granted lease listed", i, name)
			ttl, err := cli.TimeToLive(cx, g.ID)
			require.NoError(t, err, "%d %s TTL", i, name)
			require.Equal(t, g.ID, ttl.ID)
			t.Logf("member %d md %s: Grant id %x, Leases %d, TTL id ok", i, name, g.ID, len(ls.Leases))
		}
		cli.Close()
	}

	// No leader: stop two members; hasleader now gives an error (the error arm), never a bad success.
	clus.Members[1].Stop(t)
	clus.Members[2].Stop(t)
	time.Sleep(3 * time.Second)
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints()})
	require.NoError(t, err)
	defer cli.Close()
	sctx, scancel := context.WithTimeout(clientv3.WithRequireLeader(base), 5*time.Second)
	defer scancel()
	_, err = cli.Leases(sctx)
	t.Logf("no leader, hasleader Leases: err=%v", err)
	require.Error(t, err)
	_, err = cli.Grant(sctx, 60)
	t.Logf("no leader, hasleader Grant: err=%v", err)
	require.Error(t, err)
}
