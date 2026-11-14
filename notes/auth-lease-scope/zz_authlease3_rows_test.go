// Evidence for notes/auth-lease-scope.md §7 (the 3-member variant), at the etcd pin 2eaeb872bc.
// Copy into tests/integration and run:
//   GOWORK=off go test ./integration/ -run 'TestAuthLease3' -count=1 -v
// The integration framework serves etcd's full peer handler (etcdhttp.NewPeerHandler: the raft
// handler and the lease handler, cluster.go:992), as an etcd binary does.
package integration

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/pkg/v3/transport"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestAuthLease3FullPeerHandler(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	// WaitLeader asks each member's Status without a token: before auth is enabled.
	lead := clus.WaitLeader(t)
	authSetupUsers(t, integration.ToGRPC(clus.Client(0)).Auth,
		[]user{{name: "u", password: "u-123", role: "ru", key: "a", end: "c"}})
	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)
	ctx := t.Context()
	srv := clus.Members[lead].Server
	require.Equal(t, srv.MemberID(), srv.Leader(), "the leader is unchanged")
	fol := (lead + 1) % 3
	rootL, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(lead).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootL.Close()
	gz, err := rootL.Grant(ctx, 600)
	require.NoError(t, err)
	_, err = rootL.Put(ctx, "z", "v", clientv3.WithLease(gz.ID))
	require.NoError(t, err)

	rootF, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(fol).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootF.Close()
	uF, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(fol).Endpoints(), Username: "u", Password: "u-123"})
	require.NoError(t, err)
	defer uF.Close()
	_, err = rootF.Get(ctx, "z") // the follower has applied the put
	require.NoError(t, err)

	// F1: at a follower the check runs locally (u refused); root's call is forwarded to the leader
	// over leasehttp and answers with the leader's lessor (keys, TTL).
	_, err = uF.TimeToLive(ctx, gz.ID, clientv3.WithAttachedKeys())
	require.ErrorContains(t, err, "permission denied")
	_, err = uF.KeepAliveOnce(ctx, gz.ID)
	require.ErrorContains(t, err, "permission denied")
	tr, err := rootF.TimeToLive(ctx, gz.ID, clientv3.WithAttachedKeys())
	require.NoError(t, err)
	require.Equal(t, [][]byte{[]byte("z")}, tr.Keys)
	require.Positive(t, tr.TTL)
	ka, err := rootF.KeepAliveOnce(ctx, gz.ID)
	require.NoError(t, err)
	require.Positive(t, ka.TTL)

	// F2: the forwarded request carries no identity and the leader's lease handler checks none:
	// leasehttp's own client calls, the ones a follower makes (v3_server.go:553, 682), sent with
	// no token over a plain peer round tripper, return the lease's keys and renew it.
	peer := clus.Members[lead].PeerURLs[0].String()
	rt, err := rafthttp.NewRoundTripper(transport.TLSInfo{}, 5*time.Second)
	require.NoError(t, err)
	lr, err := leasehttp.TimeToLiveHTTP(ctx, lease.LeaseID(gz.ID), true, peer+leasehttp.LeaseInternalPrefix, rt)
	require.NoError(t, err)
	require.Equal(t, [][]byte{[]byte("z")}, lr.LeaseTimeToLiveResponse.Keys)
	ttl, err := leasehttp.RenewHTTP(ctx, lease.LeaseID(gz.ID), peer+leasehttp.LeasePrefix, rt)
	require.NoError(t, err)
	require.Positive(t, ttl)

	// F3: Grant and Revoke through a follower go through raft; the revocation is decided at
	// apply (permission denied for u), the grant by the follower's requireAuthInfo only.
	_, err = uF.Revoke(ctx, gz.ID)
	require.ErrorContains(t, err, "permission denied")
	gu, err := uF.Grant(ctx, 600)
	require.NoError(t, err)
	_, err = uF.Put(ctx, "a", "v", clientv3.WithLease(gu.ID))
	require.NoError(t, err)
	_, err = uF.Revoke(ctx, gu.ID)
	require.NoError(t, err)
	gr, err := rootL.Get(ctx, "a")
	require.NoError(t, err)
	require.Empty(t, gr.Kvs)
}
