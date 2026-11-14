// Copy into tests/integration at the etcd fork pin 2eaeb872b (notes/auth3-scope.md, section 3).
// After AuthEnable has returned to the administrator, a member that has not applied it yet (here a
// follower cut off from the others, as a slow member would be for a moment) still serves with
// auth off what it serves from its own state: an unauthenticated watch from revision 1 of a key
// reports its put, and a serializable read returns it. Authenticate and a linearizable read wait
// instead (ReadIndex: here, cut off, they time out rather than answer with auth off), and writes
// are checked at apply, after AuthEnable in the log, on every member.
package integration

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestAuth3LaggingMemberServesWithAuthOff(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	fol := (lead + 1) % 3
	other := (lead + 2) % 3

	_, err := clus.Client(lead).Put(t.Context(), "secret", "s")
	require.NoError(t, err)
	// the follower has the put applied
	_, err = clus.Client(fol).Get(t.Context(), "secret")
	require.NoError(t, err)

	clus.Members[fol].InjectPartition(t, clus.Members[lead], clus.Members[other])
	authSetupRoot(t, integration.ToGRPC(clus.Client(lead)).Auth)

	// anonymous, through the leader: refused
	_, err = clus.Client(lead).Get(t.Context(), "secret")
	require.Error(t, err)

	// anonymous, through the lagging follower: a watch from revision 1 reports the put
	wctx, wcancel := context.WithTimeout(t.Context(), 3*time.Second)
	defer wcancel()
	var evs int
	for wresp := range clus.Client(fol).Watch(wctx, "secret", clientv3.WithRev(1)) {
		require.NoError(t, wresp.Err())
		evs += len(wresp.Events)
		if evs > 0 {
			break
		}
	}
	require.Positivef(t, evs, "the lagging member's watch reported nothing")

	// a serializable read there returns the key
	g, err := clus.Client(fol).Get(t.Context(), "secret", clientv3.WithSerializable())
	require.NoError(t, err)
	require.Len(t, g.Kvs, 1)

	// Authenticate there is linearizable (v3_server.go:838): it does not answer
	// ErrAuthNotEnabled, it waits for the member to apply past AuthEnable (here: times out)
	actx, acancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer acancel()
	_, err = integration.ToGRPC(clus.Client(fol)).Auth.Authenticate(actx,
		&pb.AuthenticateRequest{Name: "root", Password: "123"})
	require.Error(t, err)
	require.NotContains(t, err.Error(), "authentication is not enabled")
}
