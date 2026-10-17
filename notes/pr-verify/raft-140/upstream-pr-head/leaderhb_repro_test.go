package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestLeaderHeartbeatCommitUnmatched: with #140 the leader sends its full commit
// index to a peer whose Match is 0.
func TestLeaderHeartbeatCommitUnmatched(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1, 2, 3))
	l := newTestRaft(1, 10, 1, storage)
	l.becomeCandidate()
	l.becomeLeader()
	l.appendEntry(pb.Entry{Data: []byte("x")})
	l.trk.Progress[1].MaybeUpdate(l.raftLog.lastIndex())
	l.trk.Progress[3].MaybeUpdate(l.raftLog.lastIndex())
	l.maybeCommit()
	l.readMessages()
	l.bcastHeartbeat()
	for _, m := range l.readMessages() {
		if m.To == 2 && m.Commit > l.trk.Progress[2].Match {
			t.Errorf("heartbeat to 2 carries Commit %d > Match %d", m.Commit, l.trk.Progress[2].Match)
		}
	}
}
