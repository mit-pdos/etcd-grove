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
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zaptest/observer"

	"go.etcd.io/etcd/pkg/v3/idutil"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	apply2 "go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// newPublishProbeServer is TestPublishV3WaitsForApplyAfterTooManyRequests's server.
func newPublishProbeServer(t *testing.T, lg *zap.Logger) (*EtcdServer, *nodeRecorder) {
	n := newNodeRecorder()
	ch := make(chan any, 1)
	ch <- &apply2.Result{}
	ctx, cancel := context.WithCancel(t.Context())
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, be) })
	srv := &EtcdServer{
		lgMu:       new(sync.RWMutex),
		lg:         lg,
		readych:    make(chan struct{}),
		Cfg:        config.ServerConfig{Logger: lg, TickMs: 1, SnapshotCatchUpEntries: DefaultSnapshotCatchUpEntries, MaxRequestBytes: 1000, ServerFeatureGate: features.NewDefaultServerFeatureGate("test", lg)},
		memberID:   1,
		r:          *newRaftNode(raftNodeConfig{lg: lg, Node: n, storage: mockstorage.NewStorageRecorder("")}),
		w:          wait.NewWithResponse(ch),
		applyWait:  wait.NewTimeList(),
		stopping:   make(chan struct{}),
		attributes: membership.Attributes{Name: "node1", ClientURLs: []string{"http://a"}},
		cluster:    &membership.RaftCluster{},
		reqIDGen:   idutil.NewGenerator(0, time.Time{}),
		authStore:  auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), nil, 0),
		be:         be,
		ctx:        ctx,
		cancel:     cancel,
	}
	return srv, n
}

// TestPublishV3ProbeApplyWaitAheadOfAppliedIndex: the waiters of applyWait are released at an
// index (here by a snapshot's trigger) that s.appliedIndex has not reached (#22516). The wait
// ends at once and publishV3 still retries in a tight loop: the case the PR description leaves
// to #22510. The test reports the count of rejections in 100 ms; it passes when there are many.
func TestPublishV3ProbeApplyWaitAheadOfAppliedIndex(t *testing.T) {
	core, logs := observer.New(zap.WarnLevel)
	lg := zap.New(core)
	srv, _ := newPublishProbeServer(t, lg)
	const committed = 3 * maxGapBetweenApplyAndCommitIndex
	srv.setCommittedIndex(committed)
	srv.applyWait.Trigger(committed) // applied index stays at 0

	donec := make(chan struct{})
	go func() {
		defer close(donec)
		srv.publishV3(time.Hour)
	}()
	time.Sleep(100 * time.Millisecond)
	close(srv.stopping)
	<-donec
	n := logs.FilterMessage("failed to publish local member to cluster through raft").Len()
	t.Logf("rejections in 100ms with applyWait ahead of s.appliedIndex: %d", n)
	if n < 100 {
		t.Fatalf("expected a tight loop, got %d rejections", n)
	}
}

// TestPublishV3ProbeStopDuringWait: a server stop while publishV3 waits after a rejection
// ends the wait and publishV3 (no proposal, no hang), with the publish timeout an hour.
func TestPublishV3ProbeStopDuringWait(t *testing.T) {
	core, logs := observer.New(zap.WarnLevel)
	lg := zap.New(core)
	srv, n := newPublishProbeServer(t, lg)
	const committed = 3 * maxGapBetweenApplyAndCommitIndex
	srv.setCommittedIndex(committed)

	donec := make(chan struct{})
	go func() {
		defer close(donec)
		srv.publishV3(time.Hour)
	}()
	deadline := time.Now().Add(5 * time.Second)
	for logs.Len() == 0 && time.Now().Before(deadline) {
		time.Sleep(time.Millisecond)
	}
	close(srv.stopping)
	select {
	case <-donec:
	case <-time.After(5 * time.Second):
		t.Fatal("publishV3 did not return after stop")
	}
	if len(n.Action()) != 0 {
		t.Fatalf("unexpected proposals: %v", n.Action())
	}
	if c := logs.FilterMessage("stopped publish because server is stopping").Len(); c != 1 {
		t.Fatalf("expected one stop message, got %d", c)
	}
}

// TestPublishV3ProbeTimeoutRetries: with the apply stuck, each wait ends at the publish timeout
// and publishV3 retries once per timeout (here 20 ms over 200 ms: about 10 rejections, not
// thousands).
func TestPublishV3ProbeTimeoutRetries(t *testing.T) {
	core, logs := observer.New(zap.WarnLevel)
	lg := zap.New(core)
	srv, _ := newPublishProbeServer(t, lg)
	const committed = 3 * maxGapBetweenApplyAndCommitIndex
	srv.setCommittedIndex(committed)

	donec := make(chan struct{})
	go func() {
		defer close(donec)
		srv.publishV3(20 * time.Millisecond)
	}()
	time.Sleep(200 * time.Millisecond)
	close(srv.stopping)
	<-donec
	c := logs.FilterMessage("failed to publish local member to cluster through raft").Len()
	t.Logf("rejections in 200ms with a 20ms timeout: %d", c)
	if c < 3 || c > 30 {
		t.Fatalf("expected about 10 rejections, got %d", c)
	}
}
