// Standalone reproduction test for etcd-io/etcd#22654
// (TestV3AlarmsDuringSnapshotInstall in tests/integration/v3_alarm_test.go).
package integration

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3AlarmsDuringSnapshotInstall ensures that reading a member's alarms
// does not race with the member installing a leader's snapshot.
func TestV3AlarmsDuringSnapshotInstall(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size:                   3,
		SnapshotCount:          10,
		SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	f := (lead + 1) % 3
	follower := clus.Members[f]
	others := []*integration.Member{clus.Members[lead], clus.Members[(lead+2)%3]}
	oldBe := follower.Server.Backend()

	follower.InjectPartition(t, others...)
	for i := 0; i < 20; i++ {
		_, err := clus.Client(lead).Put(t.Context(), "foo", "bar")
		require.NoError(t, err)
	}

	ctx, cancel := context.WithCancel(t.Context())
	donec := make(chan struct{})
	go func() {
		defer close(donec)
		for ctx.Err() == nil {
			follower.Server.Alarms()
		}
	}()
	follower.RecoverPartition(t, others...)
	_, err := clus.Client(f).Get(t.Context(), "foo")
	cancel()
	<-donec
	require.NoError(t, err)
	require.NotEqual(t, oldBe, follower.Server.Backend(), "the follower installed no snapshot")
}
