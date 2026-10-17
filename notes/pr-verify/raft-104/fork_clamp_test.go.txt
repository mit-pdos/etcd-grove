package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func u(x uint64) *uint64 { return &x }

func TestForkClampNeverRepaired(t *testing.T) {
	s1 := newTestMemoryStorage(withPeers(1, 2, 3))
	s1.Append([]*pb.Entry{{Index: u(1), Term: u(1)}})
	s1.SetHardState(&pb.HardState{Term: u(1), Commit: u(1)})
	r1 := newTestRaft(1, 10, 1, s1)
	r1.becomeCandidate()
	r1.becomeLeader()
	mustAppendEntry(r1, &pb.Entry{Data: []byte("new-3")}, &pb.Entry{Data: []byte("new-4")}, &pb.Entry{Data: []byte("new-5")})
	nextEnts(r1, s1)
	r1.raftLog.commitTo(5)
	pr := r1.trk.Progress[2]
	pr.Match, pr.Next = 5, 6
	pr.BecomeReplicate()
	r1.readMessages()

	s2 := newTestMemoryStorage(withPeers(1, 2, 3))
	s2.Append([]*pb.Entry{{Index: u(1), Term: u(1)}, {Index: u(2), Term: u(1)}, {Index: u(3), Term: u(1)}})
	s2.SetHardState(&pb.HardState{Term: u(1), Commit: u(1)})
	r2 := newTestRaft(2, 10, 1, s2)
	for round := 0; round < 50; round++ {
		r1.Step(&pb.Message{From: u(1), To: u(1), Type: pb.MsgBeat.Enum()})
		mustAppendEntry(r1, &pb.Entry{Data: []byte("more")})
		for i := 0; i < 10; i++ {
			for _, m := range r1.readMessages() {
				if m.GetTo() == 2 {
					if round < 2 && m.GetType() != pb.MsgHeartbeat {
						t.Logf("L->F %v idx=%d n=%d", m.GetType(), m.GetIndex(), len(m.GetEntries()))
					}
					r2.Step(m)
				}
			}
			nextEnts(r1, s1)
			nextEnts(r2, s2)
			for _, m := range r2.readMessages() {
				if m.GetTo() == 1 {
					if round < 2 && m.GetType() != pb.MsgHeartbeatResp {
						t.Logf("F->L %v idx=%d rej=%v; pr=%v", m.GetType(), m.GetIndex(), m.GetReject(), r1.trk.Progress[2])
					}
					r1.Step(m)
				}
			}
		}
	}
	t.Logf("follower committed %d last %d", r2.raftLog.committed, r2.raftLog.lastIndex())
	for i := uint64(2); i <= 3; i++ {
		t1, _ := r1.raftLog.term(i)
		t2, _ := r2.raftLog.term(i)
		if t1 != t2 {
			t.Errorf("entry %d: leader term %d, follower term %d", i, t1, t2)
		}
	}
}
