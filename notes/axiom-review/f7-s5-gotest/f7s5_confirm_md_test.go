// F7 S5 confirming review (2026-11-26): what AuthInfoFromCtx makes of the outgoing metadata, case by
// case, through clientv3 and grpc v1.84 (one member suffices: the reading is member-local).
// Each case reports the user the server bound (via a linearizable Get on a root-only key and
// Leases, admin-only) or the error.
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

func TestF7S5ConfirmMetadata(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	api0 := integration.ToGRPC(clus.Client(0))
	authSetupUsers(t, api0.Auth, []user{{name: "alice", password: "pw", role: "r", key: "a", end: "b"}})
	authSetupRoot(t, api0.Auth)

	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Minute)
	defer cancel()
	eps := clus.Client(0).Endpoints()
	anon, err := integration.NewClient(t, clientv3.Config{Endpoints: eps})
	require.NoError(t, err)
	defer anon.Close()
	rt, err := anon.Authenticate(ctx, "root", "123")
	require.NoError(t, err)
	at, err := anon.Authenticate(ctx, "alice", "pw")
	require.NoError(t, err)
	root, alice := rt.Token, at.Token

	// Leases is admin-only: success means the server bound root.
	probe := func(name string, cx context.Context) {
		op := func(f func(context.Context) error) error {
			c, cc := context.WithTimeout(cx, 8*time.Second)
			defer cc()
			return f(c)
		}
		lerr := op(func(c context.Context) error { _, e := anon.RoleList(c); return e })       // admin only: success means root
		perr := op(func(c context.Context) error { _, e := anon.Put(c, "a1", "v"); return e }) // alice may write [a,b); root too
		zerr := op(func(c context.Context) error { _, e := anon.Put(c, "z", "v"); return e })  // root only
		t.Logf("CASE %-55s RoleList(admin)=%v | Put(a1)=%v | Put(z)=%v", name, lerr, perr, zerr)
	}
	app := func(kv ...string) context.Context { return metadata.AppendToOutgoingContext(ctx, kv...) }
	raw := func(md metadata.MD) context.Context { return metadata.NewOutgoingContext(ctx, md) }

	probe("none", ctx)
	probe("token=root", app("token", root))
	probe("authorization=root", app("authorization", root))
	probe("token=alice, authorization=root", app("token", alice, "authorization", root))
	probe("authorization=root, token=alice (order swapped)", app("authorization", root, "token", alice))
	probe("token=\"\", authorization=root", app("token", "", "authorization", root))
	probe("token=badtoken, authorization=root", app("token", "badtoken", "authorization", root))
	probe("authorization=[root, badtoken]", app("authorization", root, "authorization", "badtoken"))
	probe("authorization=[badtoken, root]", app("authorization", "badtoken", "authorization", root))
	probe("token=[alice, root]", app("token", alice, "token", root))
	probe("authorization=\"Bearer \"+root", app("authorization", "Bearer "+root))
	probe("token=\"Bearer \"+root", app("token", "Bearer "+root))
	probe("authorization=\"bearer \"+root (lower b)", app("authorization", "bearer "+root))
	probe("authorization=\"Bearer  \"+root (two spaces)", app("authorization", "Bearer  "+root))
	probe("authorization=\"Bearer Bearer \"+root", app("authorization", "Bearer Bearer "+root))
	probe("authorization=\" \"+root (leading space)", app("authorization", " "+root))
	probe("authorization=\"\"", app("authorization", ""))
	probe("Append key \"Authorization\"=root (upper case)", app("Authorization", root))
	probe("Append key \"TOKEN\"=root (upper case)", app("TOKEN", root))
	probe("NewOutgoingContext MD{\"Authorization\": root} (raw)", raw(metadata.MD{"Authorization": {root}}))
	probe("NewOutgoingContext MD{\"authorization\": root} (raw)", raw(metadata.MD{"authorization": {root}}))
	probe("NewOutgoingContext MD{\"token\": {}} + authorization=root", metadata.AppendToOutgoingContext(raw(metadata.MD{"token": {}}), "authorization", root))
	probe("authorization=root\"-bin\" key", app("authorization-bin", root))

	// A user client (P = some alice) whose own token wins over an added authorization=root.
	ac, err := integration.NewClient(t, clientv3.Config{Endpoints: eps, Username: "alice", Password: "pw"})
	require.NoError(t, err)
	defer ac.Close()
	_, lerr := ac.RoleList(app("authorization", root))
	t.Logf("CASE %-55s RoleList(admin)=%v", "alice client + authorization=root", lerr)
	_, lerr = ac.RoleList(app("token", root))
	t.Logf("CASE %-55s RoleList(admin)=%v", "alice client + token=root (creds' token first)", lerr)
	_, lerr = ac.RoleList(ctx)
	t.Logf("CASE %-55s RoleList(admin)=%v", "alice client, no metadata", lerr)
}
