package etcdserver

import (
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
)

var _ backend.Backend

// Review: a restart from a raft-storage snapshot at index snapIndex leaves
// s.appliedIndex/s.term at 0 (run() sets only ep.appliedi), until the first
// entry is applied; meanwhile the first Ready's updateCommittedIndex raises
// committedIndex, so exceedsRequestLimit(0, ci) holds in that window.
func TestReviewRestartAppliedIndexZero(t *testing.T) {
	const snapIndex, snapTerm = uint64(maxGapBetweenApplyAndCommitIndex) + 1000, uint64(3)
	lg := zaptest.NewLogger(t)
	n := newNopReadyNode()
	cl := membership.NewCluster(lg)
	be, _ := betesting.NewDefaultTmpBackend(t)
	cl.SetBackend(schema.NewMembershipBackend(lg, be))
	ms := raft.NewMemoryStorage()
	cs := &raftpb.ConfState{Voters: []uint64{1}}
	require.NoError(t, ms.ApplySnapshot(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(snapIndex), Term: new(snapTerm), ConfState: cs}}))
	r := newRaftNode(raftNodeConfig{lg: lg, isIDRemoved: func(uint64) bool { return false }, Node: n,
		transport: newNopTransporter(), storage: mockstorage.NewStorageRecorder(t.TempDir()), raftStorage: ms})
	ci := cindex.NewConsistentIndex(be)
	s := &EtcdServer{lgMu: new(sync.RWMutex), lg: lg,
		Cfg: config.ServerConfig{Logger: lg, DataDir: t.TempDir(), SnapshotCatchUpEntries: DefaultSnapshotCatchUpEntries,
			ServerFeatureGate: features.NewDefaultServerFeatureGate("test", lg)},
		r: *r, cluster: cl, consistIndex: ci, firstCommitInTerm: notify.NewNotifier(),
		lessor: &lease.FakeLessor{}, uberApply: uberApplierMock{}}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	s.be = be
	s.start()
	defer s.Stop()
	time.Sleep(200 * time.Millisecond)
	t.Logf("after restart: appliedIndex=%d term=%d committedIndex=%d (raft storage snapshot %d/%d)",
		s.getAppliedIndex(), s.getTerm(), s.getCommittedIndex(), snapIndex, snapTerm)
	require.Equal(t, uint64(0), s.getAppliedIndex())
	require.Equal(t, uint64(0), s.getTerm())
	t.Logf("exceedsRequestLimit(applied=0, committed=%d) = %v", snapIndex+1, exceedsRequestLimit(0, snapIndex+1, nil, false))
	// the first entry after the snapshot repairs it
	applied := s.applyWait.Wait(snapIndex + 1)
	n.readyc <- raft.Ready{CommittedEntries: []*raftpb.Entry{{Index: new(snapIndex + 1), Term: new(snapTerm + 1), Type: raftpb.EntryNormal.Enum()}}}
	select {
	case <-applied:
	case <-time.After(10 * time.Second):
		t.Fatal("timeout")
	}
	t.Logf("after first entry: appliedIndex=%d term=%d committedIndex=%d", s.getAppliedIndex(), s.getTerm(), s.getCommittedIndex())
}

var _ rafthttp.Transporter
