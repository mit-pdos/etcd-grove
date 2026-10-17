package concurrency_test

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	integration2 "go.etcd.io/etcd/tests/v3/framework/integration"
)

// Two Mutex handles on one session share the key pfx/<lease>. m2 adopts m1's incarnation; m1
// unlocks and locks again (new incarnation); m2.Unlock then returns nil but deletes nothing.
func TestReviewProbeSameSessionStaleHandle(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()
	ctx := context.Background()
	s, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s.Close()
	m1 := concurrency.NewMutex(s, "lk")
	m2 := concurrency.NewMutex(s, "lk")
	require.NoError(t, m1.Lock(ctx))
	require.NoError(t, m2.Lock(ctx))
	c1 := m1.Header().Revision
	require.NoError(t, m1.Unlock(ctx))
	require.NoError(t, m1.Lock(ctx))
	g, _ := cli.Get(ctx, m1.Key())
	c2 := g.Kvs[0].CreateRevision
	err = m2.Unlock(ctx)
	g2, _ := cli.Get(ctx, m1.Key())
	t.Logf("c1=%d c2=%d; stale m2.Unlock err=%v; key present after: %d kv(s) (createRev %v)", c1, c2, err, len(g2.Kvs), func() any {
		if len(g2.Kvs) > 0 {
			return g2.Kvs[0].CreateRevision
		}
		return nil
	}())
	// m2 is retired: a second Unlock is ErrLockReleased, so the caller cannot tell it deleted nothing.
	t.Logf("second m2.Unlock: %v", m2.Unlock(ctx))
}

// Unlock's Txn compare needs read permission on the key; DeleteRange needs only write.
func TestReviewProbeUnlockNeedsRead(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	root := clus.RandClient()
	ctx := context.Background()
	_, err := root.RoleAdd(ctx, "root")
	require.NoError(t, err)
	_, err = root.UserAdd(ctx, "root", "rootpw")
	require.NoError(t, err)
	_, err = root.UserGrantRole(ctx, "root", "root")
	require.NoError(t, err)
	_, err = root.RoleAdd(ctx, "r")
	require.NoError(t, err)
	_, err = root.RoleGrantPermission(ctx, "r", "lk/", clientv3.GetPrefixRangeEnd("lk/"), clientv3.PermissionType(clientv3.PermReadWrite))
	require.NoError(t, err)
	_, err = root.UserAdd(ctx, "u", "upw")
	require.NoError(t, err)
	_, err = root.UserGrantRole(ctx, "u", "r")
	require.NoError(t, err)
	_, err = root.AuthEnable(ctx)
	require.NoError(t, err)

	rc, err := integration2.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "root", Password: "rootpw"})
	require.NoError(t, err)
	defer rc.Close()
	uc, err := integration2.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "u", Password: "upw"})
	require.NoError(t, err)
	defer uc.Close()

	s, err := concurrency.NewSession(uc)
	require.NoError(t, err)
	defer s.Close()
	m := concurrency.NewMutex(s, "lk")
	require.NoError(t, m.Lock(ctx))
	// write-only now
	_, err = rc.RoleRevokePermission(ctx, "r", "lk/", clientv3.GetPrefixRangeEnd("lk/"))
	require.NoError(t, err)
	_, err = rc.RoleGrantPermission(ctx, "r", "lk/", clientv3.GetPrefixRangeEnd("lk/"), clientv3.PermissionType(clientv3.PermWrite))
	require.NoError(t, err)
	err = m.Unlock(ctx)
	t.Logf("write-only user: fenced Unlock err=%v", err)
	_, derr := uc.Delete(ctx, m.Key())
	t.Logf("write-only user: plain Delete (the old Unlock) err=%v", derr)
	// a write-only user cannot Lock in the first place
	m2 := concurrency.NewMutex(s, "lk2")
	_, _ = rc.RoleGrantPermission(ctx, "r", "lk2/", clientv3.GetPrefixRangeEnd("lk2/"), clientv3.PermissionType(clientv3.PermWrite))
	t.Logf("write-only user: Lock err=%v", m2.Lock(ctx))
}
