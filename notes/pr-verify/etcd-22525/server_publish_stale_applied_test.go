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

package etcdserver

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/errors"
)

// TestReadyBySnapshotWithStaleAppliedIndex probes etcd-io/etcd#22525 together with the stale
// applied index after a snapshot (etcd-io/etcd#22528, fixed by #22529/#22510): a member that
// joins an idle cluster and installs the leader's snapshot has its committed index at the
// snapshot's index but its applied index still 0, since applySnapshot does not advance it. With
// #22525 it becomes ready on the snapshot (here simulated: the committed index set as raft
// would, the membership updated and the notifier notified as applySnapshot does), and then
// rejects every write with "too many requests" until another member's write is applied. Needs the
// PR's server_test.go (newPublishTestServer).
func TestReadyBySnapshotWithStaleAppliedIndex(t *testing.T) {
	n := newNodeRecorderStream()
	cl := membership.NewClusterFromMembers(zaptest.NewLogger(t), 1, []*membership.Member{{ID: 1}})
	srv := newPublishTestServer(t, n, cl)

	published := make(chan struct{})
	go func() {
		defer close(published)
		srv.publishV3(time.Hour)
	}()
	_, err := n.Wait(1)
	require.NoError(t, err)

	// The leader's snapshot at index 20000 holds the attributes; raft reports its commit
	// (updateCommittedIndex), applySnapshot restores the membership and notifies, and leaves
	// s.appliedIndex at 0.
	srv.setCommittedIndex(20000)
	cl.UpdateAttributes(1, srv.attributes, membership.ApplyV2storeOnly)
	srv.snapshotApplied.Notify()
	select {
	case <-published:
	case <-time.After(10 * time.Second):
		t.Fatal("publishV3 did not return after the snapshot")
	}
	select {
	case <-srv.ReadyNotify():
	default:
		t.Fatal("not ready")
	}
	require.Equal(t, uint64(0), srv.AppliedIndex())

	// Ready, but a write through it is rejected before it reaches raft.
	_, err = srv.raftRequest(context.Background(), &pb.InternalRaftRequest{Put: &pb.PutRequest{Key: []byte("k")}})
	require.ErrorIs(t, err, errors.ErrTooManyRequests)
}
