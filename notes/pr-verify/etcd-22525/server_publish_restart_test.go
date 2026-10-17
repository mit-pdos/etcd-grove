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
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
)

// A probe of etcd-io/etcd#22525's description ("A member that restarts with its attributes
// already in its own store still publishes through raft, as before"). Needs the PR's
// server_test.go (newPublishTestServer, newNodeRecorderStream).

// TestPublishV3RestartWaitsWithoutSnapshot: a member whose store already holds its attributes
// (a restart) still waits for its own entry when no snapshot is applied.
func TestPublishV3RestartWaitsWithoutSnapshot(t *testing.T) {
	n := newNodeRecorderStream()
	cl := membership.NewClusterFromMembers(zaptest.NewLogger(t), 1, []*membership.Member{{ID: 1}})
	srv := newPublishTestServer(t, n, cl)
	cl.UpdateAttributes(1, srv.attributes, membership.ApplyV2storeOnly)

	published := make(chan struct{})
	go func() {
		defer close(published)
		srv.publishV3(time.Hour)
	}()
	_, err := n.Wait(1)
	require.NoError(t, err)
	select {
	case <-published:
		t.Fatal("publish returned without its entry or a snapshot")
	case <-time.After(200 * time.Millisecond):
	}
	srv.cancel() // end the attempt (s.ctx); the loop then retries: stop it
	close(srv.stopping)
}

// TestPublishV3RestartCompletedBySnapshot: the same member becomes ready, without its entry, as
// soon as any snapshot is applied during the attempt: the attributes it already had count as
// published. Correct (they are equal to what it proposes), but the description's "still
// publishes through raft" holds only while no snapshot arrives.
func TestPublishV3RestartCompletedBySnapshot(t *testing.T) {
	n := newNodeRecorderStream()
	cl := membership.NewClusterFromMembers(zaptest.NewLogger(t), 1, []*membership.Member{{ID: 1}})
	srv := newPublishTestServer(t, n, cl)
	cl.UpdateAttributes(1, srv.attributes, membership.ApplyV2storeOnly)

	published := make(chan struct{})
	go func() {
		defer close(published)
		srv.publishV3(time.Hour)
	}()
	_, err := n.Wait(1)
	require.NoError(t, err)
	srv.snapshotApplied.Notify()
	select {
	case <-published:
	case <-time.After(10 * time.Second):
		t.Fatal("publishV3 did not return after a snapshot")
	}
	select {
	case <-srv.ReadyNotify():
	default:
		t.Fatal("not ready")
	}
}
