package raft

import (
	"testing"

	"github.com/stretchr/testify/require"
	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

func leaderWithSnap(t *testing.T) *raft {
	storage := newTestMemoryStorage(withPeers(1, 2))
	sm := newTestRaft(1, 10, 1, storage)
	sm.restore(testingSnap) // log starts after 11, commit 11
	sm.becomeCandidate()
	sm.becomeLeader()
	sm.readMessages()
	return sm
}

// etcd-style report: the index of the snapshot the leader sent (<= commit), but the
// follower never applied it (MsgSnap dropped / follower crashed before persisting).
// The next heartbeat carries Commit = min(Match, committed) past the follower's log.
func TestReviewReportUnappliedPanicsFollower(t *testing.T) {
	sm := leaderWithSnap(t)
	// follower 2 rejects a probe: leader needs to send a snapshot
	pr := sm.trk.Progress[2]
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgAppResp, Term: sm.Term,
		Index: pr.Next - 1, Reject: true, RejectHint: 0}))
	var snapIdx uint64
	for _, m := range sm.readMessages() {
		if m.Type == pb.MsgSnap {
			snapIdx = m.Snapshot.Metadata.Index
		}
	}
	require.Equal(t, uint64(11), snapIdx)
	require.Equal(t, tracker.StateSnapshot, pr.State)
	// the MsgSnap is lost; the application nonetheless reports Finish with its index
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus,
		AppliedSnapshotIndex: snapIdx}))
	require.Equal(t, uint64(11), pr.Match)
	require.NoError(t, sm.Step(pb.Message{From: 1, To: 1, Type: pb.MsgBeat}))
	var hb pb.Message
	for _, m := range sm.readMessages() {
		if m.Type == pb.MsgHeartbeat && m.To == 2 {
			hb = m
		}
	}
	t.Logf("heartbeat to 2: commit=%d", hb.Commit)
	f := newTestRaft(2, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	require.Panics(t, func() { _ = f.Step(hb) })
}

// The zero ("backward compatible") report: once unpaused, the leader probes from 1,
// which is compacted, and sends a second snapshot.
func TestReviewZeroReportResendsSnapshot(t *testing.T) {
	sm := leaderWithSnap(t)
	pr := sm.trk.Progress[2]
	pr.BecomeSnapshot(11)
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus}))
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgHeartbeatResp, Term: sm.Term}))
	snaps := 0
	for _, m := range sm.readMessages() {
		if m.Type == pb.MsgSnap {
			snaps++
		}
	}
	require.Equal(t, 1, snaps)
	require.Equal(t, tracker.StateSnapshot, pr.State)
}

// A stale Finish for an earlier snapshot lowers Match below what the follower acked.
func TestReviewStaleReportLowersMatch(t *testing.T) {
	sm := leaderWithSnap(t)
	pr := sm.trk.Progress[2]
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgAppResp, Term: sm.Term,
		Index: sm.raftLog.lastIndex()}))
	m := pr.Match
	pr.BecomeSnapshot(m) // a later snapshot episode
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus,
		AppliedSnapshotIndex: 5}))
	require.Equal(t, uint64(5), pr.Match, "was %d", m)
}

// sentCommit after OnSnapshotApplied(below the snapshot)+BecomeReplicate.
func TestReviewSentCommitAboveNext(t *testing.T) {
	sm := leaderWithSnap(t)
	pr := sm.trk.Progress[2]
	last := sm.raftLog.lastIndex()
	pr.BecomeSnapshot(last)
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus,
		AppliedSnapshotIndex: last - 1}))
	t.Logf("%s; sentCommit-ish via CanBumpCommit(last)=%v", pr, pr.CanBumpCommit(last))
	require.Equal(t, tracker.StateReplicate, pr.State)
}

// uint64 wrap.
func TestReviewWrap(t *testing.T) {
	sm := leaderWithSnap(t)
	pr := sm.trk.Progress[2]
	pr.BecomeSnapshot(11)
	require.NoError(t, sm.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus,
		AppliedSnapshotIndex: ^uint64(0)}))
	t.Logf("%s", pr)
}
