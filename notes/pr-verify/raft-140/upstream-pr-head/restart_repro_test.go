package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRestartedFollowerLearnsCommitFromHeartbeat: a follower restarts holding
// every entry of the leader's log but an older commit index (it crashed before
// learning the last commit). The leader has nothing new to append, and its
// Progress for the follower is StateReplicate with Match = lastIndex, so it sends
// no MsgApp: heartbeats are the only way the follower learns the commit index.
func TestRestartedFollowerLearnsCommitFromHeartbeat(t *testing.T) {
	ents := []pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 1}, {Index: 3, Term: 1}}

	s1 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s1.Append(ents); err != nil {
		t.Fatal(err)
	}
	s1.SetHardState(pb.HardState{Term: 1})
	l := newTestRaft(1, 10, 1, s1)
	l.becomeCandidate()
	l.becomeLeader() // term 2, appends the empty entry 4/2
	last := l.raftLog.lastIndex()
	for _, id := range []uint64{2, 3} {
		l.Step(pb.Message{From: id, To: 1, Term: l.Term, Type: pb.MsgAppResp, Index: last})
	}
	if l.raftLog.committed != last {
		t.Fatalf("leader committed = %d, want %d", l.raftLog.committed, last)
	}
	l.readMessages()

	// Follower 3, restarted: all entries, commit 3.
	s3 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s3.Append(append(ents, pb.Entry{Index: 4, Term: 2})); err != nil {
		t.Fatal(err)
	}
	s3.SetHardState(pb.HardState{Term: 2, Vote: 1, Commit: 3})
	f := newTestRaft(3, 10, 1, s3)

	for round := 0; round < 5; round++ {
		l.Step(pb.Message{From: 1, To: 1, Type: pb.MsgBeat})
		for _, m := range l.readMessages() {
			if m.To != 3 {
				continue
			}
			f.Step(m)
			for _, r := range f.readMessages() {
				l.Step(r)
			}
		}
	}
	if f.raftLog.committed != last {
		t.Errorf("follower committed = %d after 5 heartbeat rounds, want %d", f.raftLog.committed, last)
	}
}
