// Review of etcd-io/etcd#19693 (fork, protobuf-go v2 raftpb/walpb).

package etcdserver

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

func addNodeEnt(term, index, id uint64) *raftpb.Entry {
	cc := &raftpb.ConfChange{Type: raftpb.ConfChangeAddNode.Enum(), NodeId: new(id)}
	return &raftpb.Entry{Type: raftpb.EntryConfChange.Enum(), Term: new(term), Index: new(index),
		Data: pbutil.MustMarshalMessage(cc)}
}

// --force-new-cluster on a member of a 3-member cluster {1,2,3} whose backend holds no conf
// state (written before v3.5, or no membership change applied since): the WAL's snapshot record
// at index 3 carries the conf state {1,2,3}. The forced restart must remove members 2 and 3.
func TestReviewForceNewClusterBackendWithoutConfState(t *testing.T) {
	cfg := restartTestConfig(t)
	cfg.ForceNewCluster = true
	w := newWAL(t, cfg)
	require.NoError(t, w.Save(hardState(1, 1, 3),
		[]*raftpb.Entry{addNodeEnt(1, 1, 1), addNodeEnt(1, 2, 2), addNodeEnt(1, 3, 3)}))
	require.NoError(t, w.SaveSnapshot(&walpb.Snapshot{Index: new(uint64(3)), Term: new(uint64(1)),
		ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}}}))
	require.NoError(t, w.Close())
	writeBackendConfState(t, cfg, 3, 1, false)

	bwal := bootstrapWALForTest(t, cfg)
	var removed, added []uint64
	for _, e := range bwal.ents {
		if e.GetType() != raftpb.EntryConfChange || e.GetIndex() <= 3 {
			continue
		}
		var cc raftpb.ConfChange
		pbutil.MustUnmarshalMessage(&cc, e.GetData())
		switch cc.GetType() {
		case raftpb.ConfChangeRemoveNode:
			removed = append(removed, cc.GetNodeId())
		case raftpb.ConfChangeAddNode:
			added = append(added, cc.GetNodeId())
		}
	}
	t.Logf("forced conf changes: added %v removed %v", added, removed)
	assert.ElementsMatch(t, []uint64{2, 3}, removed, "force-new-cluster does not remove the other members")
}
