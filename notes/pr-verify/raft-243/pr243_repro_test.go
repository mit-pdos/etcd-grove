package raft

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.etcd.io/raft/v3/tracker"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A leader of {1,2,3} appends entries that no follower has acknowledged. Peer 2
// is in StateSnapshot. A SnapshotFinish report for peer 2 with an index past
// what peer 2 holds raises its Match to that index, and the leader commits
// entries that only it holds, once any MsgAppResp makes it recompute its commit
// index. Before this change a SnapshotFinish report never moved Match.
func TestPR243SnapStatusRaisesMatchUnacked(t *testing.T) {
	sm := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	sm.becomeCandidate()
	sm.becomeLeader()
	sm.readMessages()
	for i := 0; i < 3; i++ {
		require.NoError(t, sm.Step(pb.Message{From: 1, To: 1, Type: pb.MsgProp,
			Entries: []pb.Entry{{Data: []byte("x")}}}))
	}
	sm.readMessages() // dropped: no follower receives anything
	last := sm.raftLog.lastIndex()
	before := sm.raftLog.committed
	require.Less(t, before, last)
	require.Equal(t, uint64(0), sm.trk.Progress[2].Match)

	sm.trk.Progress[2].BecomeSnapshot(before)
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus,
		AppliedSnapshotIndex: last}))

	require.Equal(t, last, sm.trk.Progress[2].Match)
	require.Equal(t, tracker.StateReplicate, sm.trk.Progress[2].State)
	// Peer 3 acknowledges only the leader's empty entry (index 1). The leader
	// recomputes its commit index on that MsgAppResp and counts peer 2's Match.
	require.NoError(t, sm.Step(pb.Message{From: 3, To: 1, Type: pb.MsgAppResp,
		Term: sm.Term, Index: 1}))
	require.Equal(t, last, sm.raftLog.committed,
		"entries committed with no follower holding them")
}

// The zero report (the "backward compatible" case) lowers a follower's Match.
func TestPR243SnapStatusZeroLowersMatch(t *testing.T) {
	sm := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	sm.becomeCandidate()
	sm.becomeLeader()
	sm.readMessages()
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgAppResp,
		Term: sm.Term, Index: sm.raftLog.lastIndex()}))
	m := sm.trk.Progress[2].Match
	require.Positive(t, m)

	sm.trk.Progress[2].BecomeSnapshot(m)
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus}))
	require.Equal(t, uint64(0), sm.trk.Progress[2].Match, "Match lowered from %d to 0", m)
	require.Equal(t, uint64(1), sm.trk.Progress[2].Next)
}

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

// A report past the leader's last index puts Match and Next past the log.
func TestPR243SnapStatusPastLastIndex(t *testing.T) {
	sm := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	sm.becomeCandidate()
	sm.becomeLeader()
	sm.readMessages()
	last := sm.raftLog.lastIndex()
	sm.trk.Progress[2].BecomeSnapshot(0)
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus,
		AppliedSnapshotIndex: last + 100}))
	require.Equal(t, last+100, sm.trk.Progress[2].Match)
	require.Equal(t, tracker.StateReplicate, sm.trk.Progress[2].State)
	require.NoError(t, sm.Step(pb.Message{From: 1, To: 1, Type: pb.MsgProp,
		Entries: []pb.Entry{{Data: []byte("x")}}}))
	for _, m := range sm.readMessages() {
		t.Logf("%s", DescribeMessage(m, nil))
	}
	t.Logf("pr=%s commit=%d last=%d", sm.trk.Progress[2], sm.raftLog.committed, sm.raftLog.lastIndex())
}
