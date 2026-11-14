// Evidence for notes/auth-lease-scope.md §7 (the 3-member variant), at the etcd pin 2eaeb872bc.
// Copy into examples/etcd/auth3 (package auth3: it uses startMember, newUserClient, barrier) and
// run: GOWORK=off go test ./etcd/auth3/ -run TestAuthLease3 -count=1 -v
// Three members started as auth3's Main starts them: the peer listener serves only
// s.RaftHandler(), as in every example (etcdstart/common.go:172, auth3.go:85).
package auth3

import (
	"context"
	"os"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

func TestAuthLease3ExamplePeers(t *testing.T) {
	dir := t.TempDir()
	wd, _ := os.Getwd()
	require.NoError(t, os.Chdir(dir))
	defer os.Chdir(wd)

	lg := zap.NewNop()
	pa := []string{"127.0.0.1:24631", "127.0.0.1:24632", "127.0.0.1:24633"}
	ca := []string{"127.0.0.1:24641", "127.0.0.1:24642", "127.0.0.1:24643"}
	peers := make([]types.URLs, 3)
	cluster := types.URLsMap{}
	for i := range pa {
		peers[i] = types.URLs{{Scheme: "http", Host: pa[i]}}
		cluster[[]string{"al3-1", "al3-2", "al3-3"}[i]] = peers[i]
	}
	srvs := make([]*etcdserver.EtcdServer, 3)
	for i := range pa {
		s, err := startMember([]string{"al3-1", "al3-2", "al3-3"}[i], peers[i], pa[i], ca[i], cluster, lg)
		require.NoError(t, err)
		srvs[i] = s
		defer s.HardStop()
	}
	for i := range ca {
		require.NoError(t, etcdstart.Serve(srvs[i], ca[i]))
	}
	c1, err := etcdstart.NewClient(ca[0], lg)
	require.NoError(t, err)
	defer c1.Close()
	require.True(t, auth.SetUp(c1))

	ctx := context.Background()
	root1, err := newUserClient(ca[0], "root", rootPw, lg)
	require.NoError(t, err)
	defer root1.Close()
	gz, err := root1.Grant(ctx, 600)
	require.NoError(t, err)
	_, err = root1.Put(ctx, "z", "v", clientv3.WithLease(gz.ID))
	require.NoError(t, err)
	for i := range ca {
		require.True(t, barrier(ca[i], lg))
	}

	leader := -1
	for i, s := range srvs {
		if uint64(s.Leader()) == uint64(s.MemberID()) {
			leader = i
		}
	}
	require.GreaterOrEqual(t, leader, 0)
	t.Logf("leader is member %d", leader+1)

	for i := range ca {
		root, err := newUserClient(ca[i], "root", rootPw, lg)
		require.NoError(t, err)
		u, err := newUserClient(ca[i], "u", uPw, lg)
		require.NoError(t, err)

		// The API-layer checks run on the receiving member, before any forwarding:
		// u is refused at every member.
		_, err = u.TimeToLive(ctx, gz.ID, clientv3.WithAttachedKeys())
		require.ErrorContains(t, err, "permission denied", "member %d", i+1)
		_, err = u.KeepAliveOnce(ctx, gz.ID)
		require.ErrorContains(t, err, "permission denied", "member %d", i+1)
		_, err = u.Leases(ctx) // member-local, no forwarding
		require.ErrorContains(t, err, "permission denied", "member %d", i+1)
		// Revoke goes through raft: refused at apply, through any member.
		_, err = u.Revoke(ctx, gz.ID)
		require.ErrorContains(t, err, "permission denied", "member %d", i+1)
		// Grant through raft from any member.
		gu, err := u.Grant(ctx, 600)
		require.NoError(t, err, "member %d", i+1)
		_, err = u.Revoke(ctx, gu.ID)
		require.NoError(t, err, "member %d", i+1)

		// Root passes the check; then a follower forwards TimeToLive and KeepAlive to the
		// leader's peer URL over leasehttp, where the examples serve only the raft handler:
		// 404, which leasehttp reads as ErrLeaseNotFound (http.go:205-206, 263-264).
		tr, terr := root.TimeToLive(ctx, gz.ID, clientv3.WithAttachedKeys())
		_, kerr := root.KeepAliveOnce(ctx, gz.ID)
		ls, lerr := root.Leases(ctx)
		require.NoError(t, lerr)
		require.NotEmpty(t, ls.Leases)
		if i == leader {
			require.NoError(t, terr)
			require.Len(t, tr.Keys, 1)
			require.NoError(t, kerr)
		} else {
			// The gRPC layer turns ErrLeaseNotFound into a reply with TTL -1 and no keys
			// (v3rpc/lease.go:67-73), and a keep-alive TTL of 0 (:137-140), which the client's
			// KeepAliveOnce reports as ErrLeaseNotFound: a live lease reported absent.
			require.NoError(t, terr, "member %d", i+1)
			require.Equal(t, int64(-1), tr.TTL, "member %d", i+1)
			require.Empty(t, tr.Keys, "member %d", i+1)
			require.ErrorContains(t, kerr, "requested lease not found", "member %d", i+1)
		}
		root.Close()
		u.Close()
	}
}
