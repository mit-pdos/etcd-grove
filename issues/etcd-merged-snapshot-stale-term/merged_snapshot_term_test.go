// Reproduction of issues/etcd-merged-snapshot-stale-term.md: copy into server/etcdserver/ and run
// `go test ./etcdserver -run '^TestMergedSnapshotTerm$'` from server/. It uses the package's test
// helpers newNopReadyNode and newSnapTransporter (server_test.go) and the harness of
// TestSnapshotOrdering: the real raftNode loop and applyAll, fed Readys by a fake raft node.
package etcdserver

import (
	"math"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/client/pkg/v3/verify"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// TestMergedSnapshotTerm ensures that a member installing a merged snapshot
// does not end up with a log term above its own term, when raft made the
// MsgSnap as leader of an older term than the entries applied before it is
// sent.
func TestMergedSnapshotTerm(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	lg := zaptest.NewLogger(t)
	n := newNopReadyNode()
	cl := membership.NewCluster(lg)
	be, _ := betesting.NewDefaultTmpBackend(t)
	cl.SetBackend(schema.NewMembershipBackend(lg, be))

	testdir := t.TempDir()

	snapdir := filepath.Join(testdir, "member", "snap")
	if err := os.MkdirAll(snapdir, 0o755); err != nil {
		t.Fatalf("couldn't make snap dir (%v)", err)
	}

	// Members 1 to 5 are the voters; members 1 and 5 have applied index 1.
	snap1 := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index:     new(uint64(1)),
		Term:      new(uint64(1)),
		ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3, 4, 5}},
	}}
	rs := raft.NewMemoryStorage()
	require.NoError(t, rs.ApplySnapshot(snap1))
	tr, snapDoneC := newSnapTransporter(lg, snapdir)
	r := newRaftNode(raftNodeConfig{
		lg:          lg,
		isIDRemoved: func(id uint64) bool { return cl.IsIDRemoved(types.ID(id)) },
		Node:        n,
		transport:   tr,
		storage:     mockstorage.NewStorageRecorder(testdir),
		raftStorage: rs,
	})
	ci := cindex.NewConsistentIndex(be)
	cfg := config.ServerConfig{
		Logger:                 lg,
		DataDir:                testdir,
		SnapshotCatchUpEntries: DefaultSnapshotCatchUpEntries,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate("test", lg),
	}

	s := &EtcdServer{
		lgMu:              new(sync.RWMutex),
		lg:                lg,
		Cfg:               cfg,
		r:                 *r,
		snapshotter:       snap.New(lg, snapdir),
		cluster:           cl,
		consistIndex:      ci,
		beHooks:           serverstorage.NewBackendHooks(lg, ci),
		lessor:            &lease.FakeLessor{},
		firstCommitInTerm: notify.NewNotifier(),
	}

	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	s.be = be

	s.start()
	defer s.Stop()

	snapMsg := func(to, term uint64) *raftpb.Message {
		return &raftpb.Message{Type: raftpb.MsgSnap.Enum(), From: new(uint64(1)), To: new(to), Term: new(term)}
	}
	entry := func(index, term uint64) *raftpb.Entry {
		return &raftpb.Entry{Index: new(index), Term: new(term), Type: raftpb.EntryNormal.Enum()}
	}

	// Member 1 made two MsgSnaps as leader of term 1, then stepped down to
	// follow member 2 at term 2, all within one Ready.
	n.readyc <- raft.Ready{
		SoftState:        &raft.SoftState{Lead: 2, RaftState: raft.StateFollower},
		HardState:        &raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(2))},
		CommittedEntries: []*raftpb.Entry{entry(2, 1)},
		Messages:         []*raftpb.Message{snapMsg(5, 1), snapMsg(4, 1)},
	}
	// Member 2 commits an entry of term 2.
	n.readyc <- raft.Ready{
		HardState:        &raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(3))},
		CommittedEntries: []*raftpb.Entry{entry(3, 2)},
	}
	// Member 1 leads term 3 and sends a MsgSnap.
	n.readyc <- raft.Ready{
		SoftState: &raft.SoftState{Lead: 1, RaftState: raft.StateLeader},
		HardState: &raftpb.HardState{Term: new(uint64(3)), Vote: new(uint64(1)), Commit: new(uint64(3))},
		Messages:  []*raftpb.Message{snapMsg(3, 3)},
	}

	// Member 5 has not heard of term 2.
	rs5 := raft.NewMemoryStorage()
	require.NoError(t, rs5.ApplySnapshot(snap1))
	require.NoError(t, rs5.SetHardState(&raftpb.HardState{Term: new(uint64(1)), Commit: new(uint64(1))}))
	r5 := raft.RestartNode(&raft.Config{
		ID:              5,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         rs5,
		MaxSizePerMsg:   math.MaxUint64,
		MaxInflightMsgs: 256,
	})
	defer r5.Stop()

	for {
		var m *snap.Message
		select {
		case m = <-snapDoneC:
		case <-time.After(10 * time.Second):
			t.Fatal("timed out waiting for the merged snapshot to member 3")
		}
		if m.GetTo() == 5 {
			require.NoError(t, r5.Step(t.Context(), m.Message))
			rd := <-r5.Ready()
			require.Falsef(t, raft.IsEmptySnap(rd.Snapshot), "member 5 did not install the MsgSnap")
			st := r5.Status()
			assert.LessOrEqualf(t, rd.Snapshot.GetMetadata().GetTerm(), st.GetTerm(),
				"last log term of member 5, at term %d, after it installs the MsgSnap", st.GetTerm())
		}
		if m.GetTo() == 3 {
			break
		}
	}
}

