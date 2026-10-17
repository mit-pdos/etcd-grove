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

const rvRejectMsg = "failed to publish local member to cluster through raft"

func rvNewServer(t *testing.T) (*EtcdServer, *observer.ObservedLogs, *nodeRecorder) {
	n := newNodeRecorder()
	ch := make(chan any, 1)
	ch <- &apply2.Result{}
	ctx, cancel := context.WithCancel(t.Context())
	core, logs := observer.New(zap.WarnLevel)
	lg := zap.New(core)
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
	return srv, logs, n
}

// After a snapshot (without #22510), applyWait has been triggered at the
// snapshot index but s.appliedIndex lags. The PR's wait then returns at once
// and publishV3 still spins, as before the PR.
func TestReviewerPublishV3SpinsAfterSnapshotTrigger(t *testing.T) {
	srv, logs, _ := rvNewServer(t)
	const committed = 3 * maxGapBetweenApplyAndCommitIndex
	srv.setCommittedIndex(committed)
	srv.applyWait.Trigger(committed) // snapshot at the committed index; appliedIndex stays 0
	donec := make(chan struct{})
	go func() { defer close(donec); srv.publishV3(time.Hour) }()
	time.Sleep(100 * time.Millisecond)
	close(srv.stopping)
	<-donec
	n := logs.FilterMessage(rvRejectMsg).Len()
	t.Logf("rejections in 100ms: %d", n)
	if n > 100 {
		t.Errorf("publishV3 still retries in a tight loop: %d rejections in 100ms", n)
	}
}

// The committed index keeps moving ahead while apply catches up: each apply
// batch ends the wait (applied >= ci-5000 for the ci read after the
// rejection), but the retry reads a newer ci and is rejected again: one
// rejection (and warning) per apply batch, not one per timeout.
func TestReviewerPublishV3RejectedOncePerApplyBatch(t *testing.T) {
	srv, logs, _ := rvNewServer(t)
	const gap = maxGapBetweenApplyAndCommitIndex + 1000
	srv.setCommittedIndex(gap)
	donec := make(chan struct{})
	go func() { defer close(donec); srv.publishV3(time.Hour) }()
	const batches = 200
	for i := uint64(1); i <= batches; i++ {
		time.Sleep(time.Millisecond)
		a := i * 100
		srv.setCommittedIndex(a + gap) // committed advances first (raft Ready)
		srv.setAppliedIndex(a)
		srv.applyWait.Trigger(a)
	}
	close(srv.stopping)
	srv.applyWait.Trigger(1 << 40)
	<-donec
	n := logs.FilterMessage(rvRejectMsg).Len()
	t.Logf("rejections over %d apply batches: %d", batches, n)
	if n > 10 {
		t.Errorf("wait ended with the limit still exceeded %d times", n)
	}
}
