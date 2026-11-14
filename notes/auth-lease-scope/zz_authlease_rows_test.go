// Evidence for notes/auth-lease-scope.md (auth-lease Scope, 2026-11-14), at the etcd pin 2eaeb872bc.
// Copy into tests/integration and run:
//   GOWORK=off go test ./integration/ -run 'TestAuthLeaseScope' -count=1 -v
package integration

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// §4 E1-E4, E6: the lease rows of notes/auth-matrix.md with auth on, one member, sequential calls.
// u may read and write [a, c); root attaches "z" (outside u's range) to lease L.
func TestAuthLeaseScopeRows(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	authSetupUsers(t, integration.ToGRPC(clus.Client(0)).Auth,
		[]user{{name: "u", password: "u-123", role: "ru", key: "a", end: "c"}})
	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)
	ep := clus.Client(0).Endpoints()

	root, err := integration.NewClient(t, clientv3.Config{Endpoints: ep, Username: "root", Password: "123"})
	require.NoError(t, err)
	defer root.Close()
	u, err := integration.NewClient(t, clientv3.Config{Endpoints: ep, Username: "u", Password: "u-123"})
	require.NoError(t, err)
	defer u.Close()
	anon, err := integration.NewClient(t, clientv3.Config{Endpoints: ep})
	require.NoError(t, err)
	defer anon.Close()
	ctx := t.Context()
	const empty = "etcdserver: user name is empty"
	const denied = "etcdserver: permission denied"

	// E1: LeaseGrant is authenticated; any authenticated user may grant.
	_, err = anon.Grant(ctx, 600)
	require.ErrorContains(t, err, empty)
	gu, err := u.Grant(ctx, 600)
	require.NoError(t, err)

	// E2: the token-less principal is refused by every lease method, keyless leases included
	// (the code is stronger than the LeaseLeases/LeaseRenew posts, which admit the empty user).
	_, err = anon.Leases(ctx)
	require.ErrorContains(t, err, empty)
	_, err = anon.KeepAliveOnce(ctx, gu.ID)
	require.ErrorContains(t, err, empty)
	_, err = anon.TimeToLive(ctx, gu.ID)
	require.ErrorContains(t, err, empty)
	_, err = anon.TimeToLive(ctx, gu.ID, clientv3.WithAttachedKeys())
	require.ErrorContains(t, err, empty)
	_, err = anon.Revoke(ctx, gu.ID)
	require.ErrorContains(t, err, empty)

	// E3: a keyless lease granted by root: u may renew, list, read with keys, and revoke it
	// (no key to check; LeaseRevoke's apply check, checkLeasePuts, checks nothing).
	gk, err := root.Grant(ctx, 600)
	require.NoError(t, err)
	_, err = u.KeepAliveOnce(ctx, gk.ID)
	require.NoError(t, err)
	_, err = u.TimeToLive(ctx, gk.ID, clientv3.WithAttachedKeys())
	require.NoError(t, err)
	_, err = u.Revoke(ctx, gk.ID)
	require.NoError(t, err)

	// E4: lease L holding "z" (root's): u is refused for every keyed row.
	gl, err := root.Grant(ctx, 600)
	require.NoError(t, err)
	_, err = root.Put(ctx, "z", "v", clientv3.WithLease(gl.ID))
	require.NoError(t, err)
	_, err = u.Put(ctx, "a", "v", clientv3.WithLease(gl.ID)) // Put with a lease: checkLeasePuts
	require.ErrorContains(t, err, denied)
	_, err = u.Txn(ctx).Then(clientv3.OpPut("a", "v", clientv3.WithLease(gl.ID))).Commit() // in a Txn (GHSA-x35m)
	require.ErrorContains(t, err, denied)
	_, err = u.TimeToLive(ctx, gl.ID, clientv3.WithAttachedKeys())
	require.ErrorContains(t, err, denied)
	_, err = u.TimeToLive(ctx, gl.ID) // without keys: authenticated only
	require.NoError(t, err)
	_, err = u.Leases(ctx) // L holds "z": every key of every lease
	require.ErrorContains(t, err, denied)
	_, err = u.KeepAliveOnce(ctx, gl.ID)
	require.ErrorContains(t, err, denied)
	_, err = u.Revoke(ctx, gl.ID)
	require.ErrorContains(t, err, denied)
	_, err = root.Leases(ctx)
	require.NoError(t, err)

	// u's own lease with u's key: everything passes for u.
	_, err = u.Put(ctx, "a", "v", clientv3.WithLease(gu.ID))
	require.NoError(t, err)
	tr, err := u.TimeToLive(ctx, gu.ID, clientv3.WithAttachedKeys())
	require.NoError(t, err)
	require.Len(t, tr.Keys, 1)
	_, err = u.KeepAliveOnce(ctx, gu.ID)
	require.NoError(t, err)

	// E6: a revocation deletes the lease's keys, with only checkLeasePuts' check at apply.
	_, err = u.Revoke(ctx, gu.ID)
	require.NoError(t, err)
	gr, err := u.Get(ctx, "a")
	require.NoError(t, err)
	require.Empty(t, gr.Kvs)

	// After root revokes L, u may list leases again.
	_, err = root.Revoke(ctx, gl.ID)
	require.NoError(t, err)
	_, err = u.Leases(ctx)
	require.NoError(t, err)
}

// §4 E7: with auth on, an expired lease is revoked by the leader's expiry loop, whose
// LeaseRevoke runs on a context with a root token minted by WithRoot; its keys are deleted.
func TestAuthLeaseScopeExpiry(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	authSetupUsers(t, integration.ToGRPC(clus.Client(0)).Auth,
		[]user{{name: "u", password: "u-123", role: "ru", key: "a", end: "c"}})
	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)
	u, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "u", Password: "u-123"})
	require.NoError(t, err)
	defer u.Close()
	ctx := t.Context()
	g, err := u.Grant(ctx, 2)
	require.NoError(t, err)
	_, err = u.Put(ctx, "a", "v", clientv3.WithLease(g.ID))
	require.NoError(t, err)
	require.Eventually(t, func() bool {
		gr, gerr := u.Get(ctx, "a")
		return gerr == nil && len(gr.Kvs) == 0
	}, 15*time.Second, 200*time.Millisecond)
}
