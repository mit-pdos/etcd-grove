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

package integration

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/tests/v3/framework/integration"
	gofail "go.etcd.io/gofail/runtime"
)

// TestMoveLeaderToRestartedMember ensures that a leader transfer to a member
// still applying the entries it replays from its WAL after a restart does not
// crash that member. Needs failpoints (`make gofail-enable`).
func TestMoveLeaderToRestartedMember(t *testing.T) {
	integration.BeforeTest(t)
	integration.SkipIfNoGoFail(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	leaderIdx := clus.WaitLeader(t)
	followerIdx := (leaderIdx + 1) % 3
	leader, follower := clus.Members[leaderIdx], clus.Members[followerIdx]
	for i := 0; i < 150; i++ {
		_, err := clus.Client(leaderIdx).Put(t.Context(), fmt.Sprintf("k%d", i), "v")
		require.NoError(t, err)
	}
	appliedIndex := leader.Server.AppliedIndex()
	require.Eventually(t, func() bool { return follower.Server.AppliedIndex() >= appliedIndex }, 10*time.Second, 10*time.Millisecond)
	follower.Stop(t)

	// Delay each follower's Advance, so that the transfer reaches the restarted
	// follower before its raft advances past the entries it replays.
	require.NoError(t, gofail.Enable("raftBeforeFollowerSend", `sleep("2s")`))
	defer func() { _ = gofail.Disable("raftBeforeFollowerSend") }()
	require.NoError(t, follower.Restart(t))
	require.Eventually(t, func() bool { return follower.Server.AppliedIndex() >= appliedIndex }, 5*time.Second, 10*time.Millisecond)

	ctx, cancel := context.WithTimeout(t.Context(), time.Second)
	defer cancel()
	// The transfer may time out; the follower must not crash.
	_ = leader.Server.MoveLeader(ctx, uint64(leader.ID()), uint64(follower.ID()))
	require.NoError(t, gofail.Disable("raftBeforeFollowerSend"))

	clus.WaitLeader(t)
	_, err := clus.Client(followerIdx).Put(t.Context(), "k", "v")
	require.NoError(t, err)
}
