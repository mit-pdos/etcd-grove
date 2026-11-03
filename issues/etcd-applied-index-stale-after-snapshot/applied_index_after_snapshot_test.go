// Reproduction of issues/etcd-applied-index-stale-after-snapshot.md: copy into tests/integration/
// and run `go test ./integration -run '^TestAppliedIndexStaleAfterSnapshotInstall$'` from tests/.
package integration

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestAppliedIndexStaleAfterSnapshotInstall: a follower that catches up by the leader's snapshot,
// in a cluster that is then quiet, should accept writes.
func TestAppliedIndexStaleAfterSnapshotInstall(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size: 3, SnapshotCount: 100, SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	f := (lead + 1) % 3
	var others []*integration.Member
	for i := range clus.Members {
		if i != f {
			others = append(others, clus.Members[i])
		}
	}
	clus.Members[f].InjectPartition(t, others...)

	// More than 5000 writes (the server's limit on committed - applied) while the follower is cut
	// off; the leader compacts its raft log past the follower's.
	kvl := integration.ToGRPC(clus.Client(lead)).KV
	for i := 0; i < 5200; i++ {
		_, err := kvl.Put(t.Context(), &pb.PutRequest{Key: []byte("k"), Value: []byte("v")})
		require.NoError(t, err)
	}
	ls := clus.Members[lead].Server

	clus.Members[f].RecoverPartition(t, others...)
	fs := clus.Members[f].Server
	deadline := time.Now().Add(20 * time.Second)
	for fs.CommittedIndex() < ls.CommittedIndex() && time.Now().Before(deadline) {
		time.Sleep(100 * time.Millisecond)
	}
	time.Sleep(2 * time.Second) // let applySnapshot finish
	require.Equal(t, ls.CommittedIndex(), fs.CommittedIndex(), "follower did not catch up")

	// The cluster is quiet: every write goes through the follower.
	kvf := integration.ToGRPC(clus.Client(f)).KV
	for i := 0; i < 5; i++ {
		_, err := kvf.Put(t.Context(), &pb.PutRequest{Key: []byte("after"), Value: []byte("x")})
		require.NoErrorf(t, err, "put %d through the follower after its snapshot install (applied %d, committed %d)",
			i, fs.AppliedIndex(), fs.CommittedIndex())
		time.Sleep(2 * time.Second)
	}
}
