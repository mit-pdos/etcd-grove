// F7 S5 review (2026-11-26): leaseCheckD's binding `P = some info.Username'`.
// A three-member cluster, auth on (simple tokens), every member in turn:
//   - anonymous and bad-token Grant/Revoke/TimeToLive(+keys)/Leases are refused before the
//     lessor changes (checked through root afterwards);
//   - a user client's calls pass as that user;
//   - the attack: an anonymous client (no "token" metadata, so outTokOk holds) that puts an
//     issued token under the server's other key, "authorization" (TokenFieldNameSwagger).
package integration

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestF7S5LeaseAuth(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	api0 := integration.ToGRPC(clus.Client(0))
	authSetupUsers(t, api0.Auth, []user{{name: "alice", password: "pw", role: "r", key: "a", end: "b"}})
	authSetupRoot(t, api0.Auth)

	root, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer root.Close()
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	l1, err := root.Grant(ctx, 600)
	require.NoError(t, err)

	countLeases := func() int {
		r, err := root.Leases(ctx)
		require.NoError(t, err)
		return len(r.Leases)
	}

	for i := 0; i < 3; i++ {
		eps := clus.Client(i).Endpoints()
		anon, err := integration.NewClient(t, clientv3.Config{Endpoints: eps})
		require.NoError(t, err)

		before := countLeases()
		badctx := metadata.AppendToOutgoingContext(ctx, "token", "badtoken")
		for _, c := range []struct {
			name string
			cx   context.Context
			want error
		}{{"anonymous", ctx, rpctypes.ErrUserEmpty}, {"badtoken", badctx, rpctypes.ErrInvalidAuthToken}} {
			_, err = anon.Grant(c.cx, 60)
			t.Logf("member %d %s Grant: %v", i, c.name, err)
			require.ErrorIs(t, err, c.want)
			_, err = anon.Revoke(c.cx, l1.ID)
			t.Logf("member %d %s Revoke: %v", i, c.name, err)
			require.ErrorIs(t, err, c.want)
			_, err = anon.TimeToLive(c.cx, l1.ID)
			t.Logf("member %d %s TimeToLive: %v", i, c.name, err)
			require.ErrorIs(t, err, c.want)
			_, err = anon.TimeToLive(c.cx, l1.ID, clientv3.WithAttachedKeys())
			t.Logf("member %d %s TimeToLive(keys): %v", i, c.name, err)
			require.ErrorIs(t, err, c.want)
			_, err = anon.Leases(c.cx)
			t.Logf("member %d %s Leases: %v", i, c.name, err)
			require.ErrorIs(t, err, c.want)
		}
		after := countLeases()
		ttl, err := root.TimeToLive(ctx, l1.ID)
		require.NoError(t, err)
		t.Logf("member %d: leases before %d after %d; l1 TTL %d", i, before, after, ttl.TTL)
		require.Equal(t, before, after)
		require.Positive(t, ttl.TTL)

		// a user client passes as its user
		alice, err := integration.NewClient(t, clientv3.Config{Endpoints: eps, Username: "alice", Password: "pw"})
		require.NoError(t, err)
		g, err := alice.Grant(ctx, 60)
		t.Logf("member %d alice Grant: %v", i, err)
		require.NoError(t, err)
		_, err = alice.TimeToLive(ctx, g.ID)
		t.Logf("member %d alice TimeToLive: %v", i, err)
		require.NoError(t, err)
		_, err = alice.Revoke(ctx, g.ID)
		t.Logf("member %d alice Revoke: %v", i, err)
		require.NoError(t, err)
		_, err = alice.Leases(ctx) // not admin: per-lease check (l1 has no keys)
		t.Logf("member %d alice Leases: %v", i, err)

		// the attack: no "token" metadata, an issued root token under "authorization"
		ar, err := anon.Authenticate(ctx, "root", "123")
		require.NoError(t, err)
		for _, v := range []string{ar.Token, "Bearer " + ar.Token} {
			actx := metadata.AppendToOutgoingContext(ctx, "authorization", v)
			md, _ := metadata.FromOutgoingContext(actx)
			t.Logf("member %d attack: outgoing token values %q (outTokOk: none)", i, md.Get("token"))
			g, err := anon.Grant(actx, 60)
			t.Logf("member %d ANONYMOUS client (P = none) Grant with authorization=%q: err=%v", i, v, err)
			if err == nil {
				_, err = anon.TimeToLive(actx, g.ID, clientv3.WithAttachedKeys())
				t.Logf("member %d   ... TimeToLive(keys): %v", i, err)
				lr, err := anon.Leases(actx)
				t.Logf("member %d   ... Leases (admin-only for others' leases): err=%v n=%d", i, err, len(lr.Leases))
				_, err = anon.Revoke(actx, g.ID)
				t.Logf("member %d   ... Revoke: %v", i, err)
			}
			_, perr := anon.Put(actx, "rootonly", "x")
			gr, gerr := anon.Get(actx, "rootonly")
			t.Logf("member %d ANONYMOUS client Put: %v; linearizable Get: err=%v kvs=%d", i, perr, gerr, func() int { if gr == nil { return -1 }; return len(gr.Kvs) }())
			// and a P = some alice client: its own "token" wins (ts[0])
			_, err = alice.Leases(actx)
			t.Logf("member %d alice Leases with authorization=root token: %v", i, err)
		}
		alice.Close()
		anon.Close()
	}
	_ = authpb.READ
	_ = pb.LeaseGrantRequest{}
}
