package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// The leader's own Progress.Commit lags its committed index: the self-ack
// carries the commit index before maybeCommit advances it.
func TestReviewLeaderOwnCommitLags(t *testing.T) {
	nt := newNetwork(nil, nil, nil)
	nt.send(pb.Message{From: 1, To: 1, Type: pb.MsgHup})
	nt.send(pb.Message{From: 1, To: 1, Type: pb.MsgProp, Entries: []pb.Entry{{Data: []byte("x")}}})
	r := nt.peers[1].(*raft)
	t.Logf("leader committed=%d own=%s p2=%s p3=%s", r.raftLog.committed, r.trk.Progress[1], r.trk.Progress[2], r.trk.Progress[3])
	if r.trk.Progress[1].Commit != r.raftLog.committed {
		t.Errorf("leader's own Commit=%d != committed=%d", r.trk.Progress[1].Commit, r.raftLog.committed)
	}
}

// A follower restored from a snapshot does not report its commit index
// (handleSnapshot's MsgAppResp has no Commit), so the leader's Commit for it stays behind.
func TestReviewSnapshotCommitNotReported(t *testing.T) {
	r1 := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	r2 := newTestRaft(2, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	r1.becomeCandidate()
	r1.becomeLeader()
	r1.readMessages()
	snap := pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 11, Term: 1, ConfState: pb.ConfState{Voters: []uint64{1, 2}}}}
	r2.Step(pb.Message{From: 1, To: 2, Type: pb.MsgSnap, Term: 1, Snapshot: &snap})
	for _, m := range r2.readMessages() {
		t.Logf("2 sends %s Index=%d Commit=%d (2 committed=%d)", m.Type, m.Index, m.Commit, r2.raftLog.committed)
		if m.Type == pb.MsgAppResp && m.Commit != r2.raftLog.committed {
			t.Errorf("snapshot reply Commit=%d, follower committed=%d", m.Commit, r2.raftLog.committed)
		}
	}
}
