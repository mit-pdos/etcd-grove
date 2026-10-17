package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func u64p(x uint64) *uint64 { return &x }

// TestRestartedFollowerLearnsCommitFromHeartbeat (on raft v3.7 with raft#140
// applied): see the report, notes/pr-verify/raft-140.md.
func TestRestartedFollowerLearnsCommitFromHeartbeat(t *testing.T) {
	ents := []*pb.Entry{
		{Index: u64p(1), Term: u64p(1)}, {Index: u64p(2), Term: u64p(1)}, {Index: u64p(3), Term: u64p(1)},
	}
	s1 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s1.Append(ents); err != nil {
		t.Fatal(err)
	}
	s1.SetHardState(&pb.HardState{Term: u64p(1)})
	l := newTestRaft(1, 10, 1, s1)
	l.becomeCandidate()
	l.becomeLeader()
	last := l.raftLog.lastIndex()
	for _, id := range []uint64{2, 3} {
		l.Step(&pb.Message{From: u64p(id), To: u64p(1), Term: u64p(l.Term), Type: pb.MsgAppResp.Enum(), Index: u64p(last)})
	}
	if l.raftLog.committed != last {
		t.Fatalf("leader committed = %d, want %d", l.raftLog.committed, last)
	}
	l.readMessages()

	s3 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s3.Append(append(ents, &pb.Entry{Index: u64p(4), Term: u64p(2)})); err != nil {
		t.Fatal(err)
	}
	s3.SetHardState(&pb.HardState{Term: u64p(2), Vote: u64p(1), Commit: u64p(3)})
	f := newTestRaft(3, 10, 1, s3)

	for round := 0; round < 5; round++ {
		l.Step(&pb.Message{From: u64p(1), To: u64p(1), Type: pb.MsgBeat.Enum()})
		for _, m := range l.readMessages() {
			if m.GetTo() != 3 {
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
