package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

func q64(x uint64) *uint64 { return &x }

// TestStaleTermAppRespRegressesNext: with CheckQuorum (or PreVote) a follower
// answers a MsgApp of an older term with an empty MsgAppResp, which send stamps
// with the follower's current term. When the old sender is the leader of that
// current term, it reads the reply as an acceptance of index 0: in StateProbe with
// Match 0 it becomes StateReplicate with Next = 1, and sends the log from index 1
// (or a snapshot), although the follower has the log up to 3.
func TestStaleTermAppRespRegressesNext(t *testing.T) {
	ents := []*pb.Entry{{Index: q64(1), Term: q64(1)}, {Index: q64(2), Term: q64(1)}, {Index: q64(3), Term: q64(1)}}
	s2 := newTestMemoryStorage(withPeers(1, 2, 3))
	s2.Append(ents)
	s2.SetHardState(&pb.HardState{Term: q64(3)})
	l := newRaft(newTestConfig(2, 10, 1, s2))
	l.becomeCandidate()
	l.becomeLeader() // term 4, Progress[3] = {StateProbe, Match 0, Next 4}
	l.readMessages()

	s3 := newTestMemoryStorage(withPeers(1, 2, 3))
	s3.Append(ents)
	s3.SetHardState(&pb.HardState{Term: q64(4), Vote: q64(2)})
	c3 := newTestConfig(3, 10, 1, s3)
	c3.CheckQuorum = true
	f := newRaft(c3)
	// A MsgApp node 2 sent as leader of term 2, delayed.
	f.Step(&pb.Message{From: q64(2), To: q64(3), Term: q64(2), Type: pb.MsgApp.Enum(), Index: q64(1), LogTerm: q64(1)})
	for _, m := range f.readMessages() {
		l.Step(m)
	}
	if pr := l.trk.Progress[3]; pr.State == tracker.StateReplicate && pr.Match == 0 {
		t.Errorf("leader took the reply to a term-2 MsgApp as an acceptance: Progress[3] = %s", pr)
	}
}
