// Reproduction of issues/etcd-alarm-store-snapshot-race.md.
//
// Copy into tests/integration/ of an etcd checkout at the pin (de825d8c6) or upstream main and run
//
//	go test -race ./integration -run 'TestV3AlarmsDuringSnapshotInstall' -count=1 -v
//
// from tests/. The race detector reports the write of EtcdServer.alarmStore in restoreAlarms
// (applySnapshot, on the apply goroutine) against its read in EtcdServer.Alarms (the maintenance
// Status RPC's goroutine).
package integration

import (
	"context"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestV3AlarmsDuringSnapshotInstall(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size: 3, SnapshotCount: 10, SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	f := (lead + 1) % 3
	fm := clus.Members[f]
	var others []*integration.Member
	for i, m := range clus.Members {
		if i != f {
			others = append(others, m)
		}
	}
	cl := clus.Client(lead)
	cf := clus.Client(f)

	oldBe := fm.Server.Backend()
	fm.InjectPartition(t, others...)
	for i := 0; i < 40; i++ {
		_, err := cl.Put(t.Context(), "k", "v")
		require.NoError(t, err)
	}

	ctx, cancel := context.WithCancel(t.Context())
	var wg sync.WaitGroup
	var calls atomic.Int64
	for r := 0; r < 8; r++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ctx.Err() == nil {
				// the maintenance Status RPC reads s.Alarms(), that is s.alarmStore
				if _, err := cf.Status(ctx, fm.GRPCURL); err == nil {
					calls.Add(1)
				}
			}
		}()
	}
	time.Sleep(50 * time.Millisecond)
	fm.RecoverPartition(t, others...)
	want := clus.Members[lead].Server.KV().Rev()
	deadline := time.Now().Add(10 * time.Second)
	for fm.Server.KV().Rev() < want && time.Now().Before(deadline) {
		time.Sleep(10 * time.Millisecond)
	}
	time.Sleep(100 * time.Millisecond)
	cancel()
	wg.Wait()
	require.GreaterOrEqual(t, fm.Server.KV().Rev(), want, "follower did not catch up")
	require.NotEqual(t, oldBe, fm.Server.Backend(), "the follower installed no snapshot")
	t.Logf("snapshot installed, %d Status calls", calls.Load())
}
