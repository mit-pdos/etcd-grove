// Review of etcd-io/etcd#19693 (upstream, gogoproto raftpb/walpb).

package etcdserver

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

func addNodeEntV(term, index, id uint64) raftpb.Entry {
	cc := raftpb.ConfChange{Type: raftpb.ConfChangeAddNode, NodeID: id}
	return raftpb.Entry{Type: raftpb.EntryConfChange, Term: term, Index: index, Data: pbutil.MustMarshal(&cc)}
}

// The data dir `etcdutl snapshot restore` writes for a new cluster {10, 20} (new member IDs,
// e.g. a new --initial-cluster-token) from a snapshot of a v3.5+ cluster {1, 2}: the WAL holds
// AddNode 10, AddNode 20 (commit 2) and a snapshot record at 2 with conf state {10, 20}, the
// backend's consistent index is forced to 2, its members are trimmed and re-added, but its
// meta "confState" key is the source cluster's {1, 2} (TrimMembershipFromBackend does not touch
// it). The member's raft must start with the voters {10, 20}.
func TestReviewRestoredBackendStaleConfState(t *testing.T) {
	cfg := restartTestConfig(t)
	w := newWAL(t, cfg)
	require.NoError(t, w.Save(raftpb.HardState{Term: 1, Vote: 10, Commit: 2},
		[]raftpb.Entry{addNodeEntV(1, 1, 10), addNodeEntV(1, 2, 20)}))
	newCS := raftpb.ConfState{Voters: []uint64{10, 20}}
	require.NoError(t, w.SaveSnapshot(walpb.Snapshot{Index: 2, Term: 1, ConfState: &newCS}))
	require.NoError(t, w.Close())
	ss := snap.New(cfg.Logger, cfg.SnapDir())
	require.NoError(t, ss.SaveSnap(raftpb.Snapshot{Data: []byte("{}"), Metadata: raftpb.SnapshotMetadata{
		Index: 2, Term: 1, ConfState: newCS}}))

	be := serverstorage.OpenBackend(cfg, nil)
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateMetaBucket(tx)
	schema.UnsafeUpdateConsistentIndex(tx, 2, 1)
	schema.MustUnsafeSaveConfStateToBackend(cfg.Logger, tx, &raftpb.ConfState{Voters: []uint64{1, 2}})
	tx.Unlock()
	require.NoError(t, be.Close())

	s, _ := bootstrapStorageForTest(t, cfg)
	_, cs, err := s.InitialState()
	require.NoError(t, err)
	t.Logf("raft starts with voters %v", cs.Voters)
	assert.ElementsMatch(t, []uint64{10, 20}, cs.Voters, "raft starts with the source cluster's voters")
}
