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

package watch

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3WatchProgressThenRestoreSnapshotCompacted checks that a watch on a
// slow follower that a progress notification told nothing changed up to
// revision P is not cancelled as compacted at a revision at or below P when
// the follower restores a leader snapshot compacted at P.
func TestV3WatchProgressThenRestoreSnapshotCompacted(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size:                   3,
		SnapshotCount:          10,
		SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	wStream, err := integration.ToGRPC(clus.Client(0)).Watch.Watch(ctx)
	require.NoError(t, err)
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: []byte("w")},
	}}))
	wresp, err := wStream.Recv()
	require.NoError(t, err)
	require.True(t, wresp.Created)

	// Other keys change; a progress notification tells the watcher that w did
	// not change up to P.
	kvc0 := integration.ToGRPC(clus.Client(0)).KV
	for i := 0; i < 5; i++ {
		_, err = kvc0.Put(ctx, &pb.PutRequest{Key: []byte("other"), Value: []byte("v")})
		require.NoError(t, err)
	}
	require.NoError(t, wStream.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_ProgressRequest{
		ProgressRequest: &pb.WatchProgressRequest{},
	}}))
	wresp, err = wStream.Recv()
	require.NoError(t, err)
	require.Empty(t, wresp.Events)
	require.Zero(t, wresp.CompactRevision)
	p := wresp.Header.Revision
	t.Logf("progress notification at revision %d", p)

	// Member 0 is cut off; the others compact at P and take snapshots past
	// member 0's log, so it will catch up from a snapshot.
	clus.Members[0].InjectPartition(t, clus.Members[1:]...)
	initialLead := clus.WaitMembersForLeader(t, clus.Members[1:]) + 1
	kvc1 := integration.ToGRPC(clus.Client(1)).KV
	_, err = kvc1.Compact(ctx, &pb.CompactionRequest{Revision: p, Physical: true})
	require.NoError(t, err)
	for i := 0; i < 15; i++ {
		_, err = kvc1.Put(ctx, &pb.PutRequest{Key: []byte("other"), Value: []byte("v")})
		require.NoError(t, err)
	}
	expectMemberLog(t, clus.Members[initialLead], 5*time.Second, "saved snapshot to disk", 2)

	clus.Members[0].RecoverPartition(t, clus.Members[1:]...)
	clus.WaitLeader(t)
	expectMemberLog(t, clus.Members[0], 5*time.Second, "received and saved database snapshot", 1)

	// w changes; the watch should report it, not a compaction at or below P.
	_, err = kvc1.Put(ctx, &pb.PutRequest{Key: []byte("w"), Value: []byte("x")})
	require.NoError(t, err)
	for {
		wresp, err = wStream.Recv()
		require.NoError(t, err)
		require.Falsef(t, wresp.CompactRevision != 0 && wresp.CompactRevision <= p,
			"watcher told nothing changed up to %d is cancelled as compacted at %d", p, wresp.CompactRevision)
		if len(wresp.Events) > 0 {
			require.Equal(t, "w", string(wresp.Events[0].Kv.Key))
			return
		}
	}
}
