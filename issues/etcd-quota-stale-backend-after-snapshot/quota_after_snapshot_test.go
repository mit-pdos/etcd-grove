// Reproduction of issues/etcd-quota-stale-backend-after-snapshot.md: copy into tests/integration/
// and run `go test ./integration -run '^TestV3StorageQuotaAfterSnapshot$'` from tests/. It uses the
// package's helper waitForRestart (v3_grpc_test.go).
package integration

import (
	"os"
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3StorageQuotaAfterSnapshot ensures that a member that catches up by a
// snapshot checks requests against the quota with the snapshot's db.
func TestV3StorageQuotaAfterSnapshot(t *testing.T) {
	integration.BeforeTest(t)
	quotasize := int64(16 * os.Getpagesize())

	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size:                   3,
		SnapshotCount:          10,
		SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)
	kvc0 := integration.ToGRPC(clus.Client(0)).KV

	key := []byte("abc")
	_, err := kvc0.Put(t.Context(), &pb.PutRequest{Key: key, Value: make([]byte, quotasize)})
	require.NoError(t, err)
	// Member 2's db grows past the quota member 2 restarts with below.
	kvc2 := integration.ToGRPC(clus.Client(2)).KV
	_, err = kvc2.Range(t.Context(), &pb.RangeRequest{Key: key})
	require.NoError(t, err)

	// While member 2 is down, the other members delete the key, compact,
	// defragment and compact their raft logs past member 2's.
	clus.Members[2].Stop(t)
	clus.WaitMembersForLeader(t, clus.Members[:2])
	dresp, err := kvc0.DeleteRange(t.Context(), &pb.DeleteRangeRequest{Key: key})
	require.NoError(t, err)
	_, err = kvc0.Compact(t.Context(), &pb.CompactionRequest{Revision: dresp.Header.Revision, Physical: true})
	require.NoError(t, err)
	for i := 0; i < 2; i++ {
		_, err = integration.ToGRPC(clus.Client(i)).Maintenance.Defragment(t.Context(), &pb.DefragmentRequest{})
		require.NoError(t, err)
	}
	for i := 0; i < 20; i++ {
		_, err = kvc0.Put(t.Context(), &pb.PutRequest{Key: []byte("foo"), Value: []byte("bar")})
		require.NoError(t, err)
	}

	// Member 2 restarts with a quota and catches up by a snapshot under it.
	clus.Members[2].QuotaBackendBytes = quotasize
	require.NoError(t, clus.Members[2].Restart(t))
	clus.WaitMembersForLeader(t, clus.Members)
	kvc2 = integration.ToGRPC(clus.Client(2)).KV
	waitForRestart(t, kvc2)
	_, err = kvc2.Range(t.Context(), &pb.RangeRequest{Key: []byte("foo")})
	require.NoError(t, err)
	size := clus.Members[2].Server.Backend().Size()
	require.Less(t, size, quotasize)

	_, err = kvc2.Put(t.Context(), &pb.PutRequest{Key: []byte("foo"), Value: []byte("bar")})
	require.NoErrorf(t, err, "put through member 2 with db size %d under quota %d", size, quotasize)
}
