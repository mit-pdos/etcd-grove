package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func p64(x uint64) *uint64 { return &x }
func ent(i, t uint64) *pb.Entry { return &pb.Entry{Index: p64(i), Term: p64(t)} }

// TestLogSyncedBogusAckStaleTail, on raft v3.7 with raft#140 applied (the port
// of the reviewer's test at the PR head; see notes/pr-verify/raft-140.md).
func TestLogSyncedBogusAckStaleTail(t *testing.T) {
	common := []*pb.Entry{ent(1, 1), ent(2, 1), ent(3, 1)}

	s2 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s2.Append(common); err != nil {
		t.Fatal(err)
	}
	s2.SetHardState(&pb.HardState{Term: p64(3), Commit: p64(1)})
	c2 := newTestConfig(2, 10, 1, s2)
	c2.MaxSizePerMsg = 1
	l := newRaft(c2)
	l.becomeCandidate()
	l.becomeLeader()
	l.readMessages()

	s3 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s3.Append(append(append([]*pb.Entry{}, common...), ent(4, 3))); err != nil {
		t.Fatal(err)
	}
	s3.SetHardState(&pb.HardState{Term: p64(4), Vote: p64(2), Commit: p64(1)})
	c3 := newTestConfig(3, 10, 1, s3)
	c3.CheckQuorum = true
	c3.MaxSizePerMsg = 1
	f := newRaft(c3)

	f.Step(&pb.Message{From: p64(2), To: p64(3), Term: p64(2), Type: pb.MsgApp.Enum(), Index: p64(1), LogTerm: p64(1), Commit: p64(1)})
	resp := f.readMessages()
	if len(resp) != 1 || resp[0].GetType() != pb.MsgAppResp || resp[0].GetTerm() != 4 || resp[0].GetIndex() != 0 {
		t.Fatalf("unexpected response %v", resp)
	}
	l.Step(resp[0])
	if pr := l.trk.Progress[3]; pr.State.String() != "StateReplicate" || pr.Match != 0 {
		t.Fatalf("leader's Progress[3] = %s", pr)
	}
	for _, m := range l.readMessages() {
		if m.GetTo() == 3 && m.GetType() == pb.MsgApp && (m.GetIndex() == 1 || m.GetIndex() == 2) {
			f.Step(m)
		}
	}
	f.readMessages()
	if !f.logSynced {
		t.Fatalf("logSynced = false")
	}
	l.Step(&pb.Message{From: p64(1), To: p64(2), Term: p64(4), Type: pb.MsgAppResp.Enum(), Index: p64(4)})
	if l.raftLog.committed != 4 {
		t.Fatalf("leader committed = %d", l.raftLog.committed)
	}
	l.readMessages()
	l.bcastHeartbeat()
	for _, m := range l.readMessages() {
		if m.GetTo() == 3 && m.GetType() == pb.MsgHeartbeat {
			f.Step(m)
		}
	}
	for i := uint64(1); i <= f.raftLog.committed; i++ {
		ft, _ := f.raftLog.term(i)
		lt, _ := l.raftLog.term(i)
		if ft != lt {
			t.Errorf("follower committed entry %d of term %d; the leader's entry %d has term %d", i, ft, i, lt)
		}
	}
}
