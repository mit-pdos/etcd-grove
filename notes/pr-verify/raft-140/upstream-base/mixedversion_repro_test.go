package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestOldFollowerUnmatchedHeartbeatCommit: a follower running the code before
// etcd-io/raft#139/#140 receives the heartbeat a leader with #140 sends to a
// peer it has not matched yet: Commit is the leader's commit index, not
// min(Match, committed) = 0. The follower's log has an uncommitted tail from an
// older term reaching past that index, so commitTo does not panic: it commits
// the stale entries.
//
// Leader 1, term 3: log 1/1 2/1 3/1 3/4 3/5 3/6, committed 6, Progress[2].Match = 0.
// Follower 2:       log 1/1 2/1 3/1 2/4 2/5 2/6 (4..6 from a term-2 leader).
func TestOldFollowerUnmatchedHeartbeatCommit(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := storage.Append([]pb.Entry{
		{Index: 1, Term: 1}, {Index: 2, Term: 1}, {Index: 3, Term: 1},
		{Index: 4, Term: 2}, {Index: 5, Term: 2}, {Index: 6, Term: 2},
	}); err != nil {
		t.Fatal(err)
	}
	f := newTestRaft(2, 10, 1, storage)
	f.becomeFollower(2, 3)

	// The new leader's first message to it may be a heartbeat (a tick, or the
	// probe was dropped).
	f.Step(pb.Message{From: 1, To: 2, Term: 3, Type: pb.MsgHeartbeat, Commit: 6})
	for i := uint64(4); i <= f.raftLog.committed; i++ {
		if term, _ := f.raftLog.term(i); term != 3 {
			t.Errorf("committed entry %d has term %d; the leader's entry %d has term 3", i, term, i)
		}
	}
}
