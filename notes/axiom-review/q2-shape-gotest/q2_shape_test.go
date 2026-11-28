// Q2 widening probe (2026-11-27): requests outside auth.reqShape (an empty or inverted range) with
// auth on. The model's verdict (kvGranted: coversRange over [key, end), vacuous when end <= key)
// grants them; Go's isOpPermitted asks the interval tree's Contains, which refuses them here.
package integration

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestQ2ShapeTxnEmptyCompareRange(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	api0 := integration.ToGRPC(clus.Client(0))
	// alice: read and write on the single key "p" only.
	authSetupUsers(t, api0.Auth, []user{{name: "alice", password: "pw", role: "ra", key: "p", end: ""}})
	authSetupRoot(t, api0.Auth)

	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	alice, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{clus.Members[0].GRPCURL}, Username: "alice", Password: "pw"})
	require.NoError(t, err)
	defer alice.Close()
	root, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{clus.Members[0].GRPCURL}, Username: "root", Password: "123"})
	require.NoError(t, err)
	defer root.Close()

	r0, err := root.Get(ctx, "p")
	require.NoError(t, err)

	// The compare's range [a, a) is empty: the model's coversRange is vacuous, so kvGranted holds
	// (the put on "p" is covered); the put is in both branches.
	_, err = alice.Txn(ctx).
		If(clientv3.Compare(clientv3.Value("a"), "=", "x").WithRange("a")).
		Then(clientv3.OpPut("p", "1")).Else(clientv3.OpPut("p", "1")).Commit()
	t.Logf("txn, compare range [a,a): err=%v", err)
	require.Error(t, err)

	// An inverted compare range [e, b).
	_, err = alice.Txn(ctx).
		If(clientv3.Compare(clientv3.Value("e"), "=", "x").WithRange("b")).
		Then(clientv3.OpPut("p", "1")).Else(clientv3.OpPut("p", "1")).Commit()
	t.Logf("txn, compare range [e,b): err=%v", err)
	require.Error(t, err)

	// A nested get of an empty range inside the transaction.
	_, err = alice.Txn(ctx).Then(clientv3.OpGet("a", clientv3.WithRange("a")), clientv3.OpPut("p", "1")).Commit()
	t.Logf("txn, get [a,a) then put p: err=%v", err)
	require.Error(t, err)

	// An inverted delete: refused by Go, a no-op in the model.
	_, err = alice.Delete(ctx, "e", clientv3.WithRange("b"))
	t.Logf("delete [e,b): err=%v", err)

	r1, err := root.Get(ctx, "p")
	require.NoError(t, err)
	t.Logf("p after: count=%d, revision %d -> %d", r1.Count, r0.Header.Revision, r1.Header.Revision)
	require.Equal(t, int64(0), r1.Count)
	require.Equal(t, r0.Header.Revision, r1.Header.Revision)
}
