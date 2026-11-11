// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package e2e

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/e2e"
)

// TestCompactZeroCrashCompactRevision: a member that crashes during a
// compaction at revision 0, after the compaction is persisted as scheduled and
// before it is recorded as finished, restarts with compact revision -1, while
// the members that finished it have 0. The members should agree.
func TestCompactZeroCrashCompactRevision(t *testing.T) {
	e2e.BeforeTest(t)

	ctx := t.Context()
	clus, err := e2e.NewEtcdProcessCluster(ctx, t,
		e2e.WithClusterSize(3),
		e2e.WithGoFailEnabled(true),
	)
	require.NoError(t, err)
	t.Cleanup(func() { clus.Stop() })

	leaderIdx := clus.WaitLeader(t)
	targetIdx := (leaderIdx + 1) % clus.Cfg.ClusterSize

	cli := newClient(t, clus.Procs[targetIdx].EndpointsGRPC(), e2e.ClientConfig{})
	putResp, err := cli.Put(ctx, "foo", "bar")
	require.NoError(t, err)
	rev := putResp.Header.Revision

	// The target member crashes in the compaction job (as in TestReproduce17780).
	require.NoError(t, clus.Procs[targetIdx].Failpoints().SetupHTTP(ctx, "compactBeforeSetFinishedCompact", `panic`))
	_, err = cli.Compact(ctx, 0, clientv3.WithCompactPhysical())
	require.Error(t, err)
	require.NoError(t, clus.Procs[targetIdx].Restart(ctx))

	compactRevs := make([]int64, len(clus.Procs))
	for i, proc := range clus.Procs {
		c := newClient(t, proc.EndpointsGRPC(), e2e.ClientConfig{})
		resp, err := c.HashKV(ctx, proc.EndpointsGRPC()[0], rev)
		require.NoError(t, err)
		compactRevs[i] = resp.CompactRevision
	}
	t.Logf("compact revisions: %v (member %d restarted)", compactRevs, targetIdx)
	assert.Equalf(t, compactRevs[leaderIdx], compactRevs[targetIdx],
		"the restarted member's compact revision should be the leader's")

	// The members that finished the compaction at 0 refuse it again.
	_, err = cli.Compact(ctx, 0)
	assert.Errorf(t, err, "Compact(0) through the restarted member should be refused as compacted")
}

// TestCompactZeroCrashCorruptAlarm: with the periodic corruption check on, the
// same crash makes the check raise a corruption alarm, which stops writes,
// once the restarted member is the leader, although no member's data differs.
// The check's period is long enough for the leadership to move to the
// restarted member before the first check: on the other members, HashKV of
// revision 0 after Compact(0) has a bug of its own.
func TestCompactZeroCrashCorruptAlarm(t *testing.T) {
	e2e.BeforeTest(t)

	ctx := t.Context()
	clus, err := e2e.NewEtcdProcessCluster(ctx, t,
		e2e.WithClusterSize(3),
		e2e.WithGoFailEnabled(true),
		e2e.WithCorruptCheckTime(10*time.Second),
	)
	require.NoError(t, err)
	t.Cleanup(func() { clus.Stop() })

	leaderIdx := clus.WaitLeader(t)
	targetIdx := (leaderIdx + 1) % clus.Cfg.ClusterSize

	cli := newClient(t, clus.Procs[targetIdx].EndpointsGRPC(), e2e.ClientConfig{})
	_, err = cli.Put(ctx, "foo", "bar")
	require.NoError(t, err)

	require.NoError(t, clus.Procs[targetIdx].Failpoints().SetupHTTP(ctx, "compactBeforeSetFinishedCompact", `panic`))
	_, err = cli.Compact(ctx, 0, clientv3.WithCompactPhysical())
	require.Error(t, err)
	require.NoError(t, clus.Procs[targetIdx].Restart(ctx))

	// The restarted member becomes the leader.
	st, err := cli.Status(ctx, clus.Procs[targetIdx].EndpointsGRPC()[0])
	require.NoError(t, err)
	leaderIdx = clus.WaitLeader(t)
	leaderCli := newClient(t, clus.Procs[leaderIdx].EndpointsGRPC(), e2e.ClientConfig{})
	_, err = leaderCli.MoveLeader(ctx, st.Header.MemberId)
	require.NoError(t, err)
	require.Equal(t, targetIdx, clus.WaitLeader(t))

	time.Sleep(12 * time.Second) // at least one check by the restarted member

	alarms, err := cli.AlarmList(ctx)
	require.NoError(t, err)
	assert.Emptyf(t, alarms.Alarms, "no member's data differs, so no alarm should be raised")
	_, err = cli.Put(ctx, "foo", "baz")
	assert.NoErrorf(t, err, "writes should be accepted")
}
