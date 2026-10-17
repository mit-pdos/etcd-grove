package raft

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.etcd.io/raft/v3/tracker"

	pb "go.etcd.io/raft/v3/raftpb"
)

// In StateSnapshot, an MsgAppResp that raises Match but still leaves the
// follower behind the leader's first index takes the follower out of
// StateSnapshot (the condition is now on Next, which BecomeSnapshot set past
// the snapshot), and the leader sends a second snapshot while the first one is
// in flight. Before this change the follower stayed in StateSnapshot.
func TestPR243AppRespInSnapshotResendsSnapshot(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1, 2))
	sm := newTestRaft(1, 10, 1, storage)
	sm.restore(testingSnap) // the log starts after index 11
	sm.becomeCandidate()
	sm.becomeLeader()
	sm.readMessages()

	pr := sm.trk.Progress[2]
	pr.BecomeSnapshot(11)
	require.Equal(t, uint64(12), sm.raftLog.firstIndex())

	// A delayed acknowledgment of index 5 (below the first index).
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgAppResp,
		Term: sm.Term, Index: 5}))
	require.Equal(t, uint64(5), pr.Match)
	var snaps int
	for _, m := range sm.readMessages() {
		if m.Type == pb.MsgSnap {
			snaps++
		}
	}
	require.Equal(t, 1, snaps, "a second snapshot sent")
	require.Equal(t, tracker.StateSnapshot, pr.State)
}
