// Copy into tests/integration of etcd-io/etcd.

package integration

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestPeriodicCheckNoCorruptAlarmDuringCompaction: a healthy one-member
// cluster with the periodic corruption check enabled, every key deleted, then
// compacted, with no other traffic. The member is not corrupt, so no CORRUPT
// alarm should be raised while the compaction deletes the old revisions.
//
// A small compaction batch makes the physical compaction take a few seconds,
// as a large one does with the default batch size.
func TestPeriodicCheckNoCorruptAlarmDuringCompaction(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	m := clus.Members[0]
	m.Stop(t)
	m.CorruptCheckTime = 20 * time.Millisecond
	m.CompactionBatchLimit = 1
	m.CompactionSleepInterval = time.Millisecond
	require.NoError(t, m.Restart(t))
	clus.WaitLeader(t)

	ctx := t.Context()
	cli := clus.Client(0)
	const n = 2000
	for i := 0; i < n; i++ {
		_, err := cli.Put(ctx, "k", "v")
		require.NoError(t, err)
	}
	dresp, err := cli.Delete(ctx, "k")
	require.NoError(t, err)
	_, err = cli.Compact(ctx, dresp.Header.Revision)
	require.NoError(t, err)

	deadline := time.Now().Add(10 * time.Second)
	for time.Now().Before(deadline) {
		aresp, err := cli.AlarmList(ctx)
		require.NoError(t, err)
		for _, a := range aresp.Alarms {
			if a.Alarm == pb.AlarmType_CORRUPT {
				t.Fatalf("CORRUPT alarm raised on a healthy member during compaction: %v", a)
			}
		}
		time.Sleep(100 * time.Millisecond)
	}
}
