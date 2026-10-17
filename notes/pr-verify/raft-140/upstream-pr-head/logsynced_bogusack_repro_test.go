package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestLogSyncedBogusAckStaleTail: a reachable schedule, with this package's own
// leader, in which a follower sets logSynced on a MsgApp that ends before the
// stale tail of its log, and a heartbeat (#140) then commits a stale entry.
//
// The leader regresses its Progress to Next = 1 on a MsgAppResp{Index: 0} that the
// follower sent in answer to a *delayed MsgApp of the leader's earlier term* (the
// m.Term < r.Term branch of Step, with CheckQuorum or PreVote): send stamps the
// response with the follower's current term, which is the leader's new term, so
// the leader takes it for an acknowledgement of index 0 and, in StateProbe with
// Match = 0, calls BecomeReplicate (Next = Match+1 = 1). It then sends the log
// from index 1, one entry per MsgApp (MaxSizePerMsg); the follower accepts the
// first, which agrees with its log and ends before its stale tail.
//
// Node 2 was leader at term 2 (a MsgApp it sent then is still in flight). Then:
//   leader 2, term 4: log 1/1 2/1 3/1 4/4 (4/4 the empty entry of becomeLeader);
//   follower 3, term 4: log 1/1 2/1 3/1 4/3 (4/3 from a term-3 leader, uncommitted).
func TestLogSyncedBogusAckStaleTail(t *testing.T) {
	common := []pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 1}, {Index: 3, Term: 1}}

	// Leader 2.
	s2 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s2.Append(common); err != nil {
		t.Fatal(err)
	}
	s2.SetHardState(pb.HardState{Term: 3, Commit: 1})
	c2 := newTestConfig(2, 10, 1, s2)
	c2.MaxSizePerMsg = 1
	l := newRaft(c2)
	l.becomeCandidate() // term 4
	l.becomeLeader()    // appends 4/4; Progress[3] = {StateProbe, Match 0, Next 4}
	l.readMessages()    // the probes (prev 3, [4/4]) are delayed: dropped here

	// Follower 3, at term 4 (it voted for 2), with the stale entry 4/3.
	s3 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s3.Append(append(common, pb.Entry{Index: 4, Term: 3})); err != nil {
		t.Fatal(err)
	}
	s3.SetHardState(pb.HardState{Term: 4, Vote: 2, Commit: 1})
	c3 := newTestConfig(3, 10, 1, s3)
	c3.CheckQuorum = true // or PreVote: etcd enables both
	c3.MaxSizePerMsg = 1
	f := newRaft(c3)

	// A delayed MsgApp of node 2's leadership at term 2 reaches 3.
	f.Step(pb.Message{From: 2, To: 3, Term: 2, Type: pb.MsgApp, Index: 1, LogTerm: 1, Commit: 1})
	resp := f.readMessages()
	if len(resp) != 1 || resp[0].Type != pb.MsgAppResp || resp[0].Term != 4 || resp[0].Index != 0 || resp[0].Reject {
		t.Fatalf("unexpected response %+v", resp)
	}
	l.Step(resp[0])
	// BecomeReplicate set Next = Match+1 = 1, and the leader at once sent entries
	// 1..4, one per MsgApp, so Next is now 5.
	if pr := l.trk.Progress[3]; pr.State.String() != "StateReplicate" || pr.Match != 0 {
		t.Fatalf("leader's Progress[3] = %s; expected StateReplicate from Match 0", pr)
	}
	// The leader now sends one MsgApp per entry from index 1 (prev 0, 1, 2, 3).
	// Deliver those of prev 1 and 2 (prev 0 is below the follower's commit index;
	// prev 3 carries 4/4, which would truncate): both agree with the follower's log
	// and end before its stale entry 4/3.
	for _, m := range l.readMessages() {
		if m.To == 3 && m.Type == pb.MsgApp && (m.Index == 1 || m.Index == 2) {
			if len(m.Entries) != 1 {
				t.Fatalf("MsgApp %+v", m)
			}
			f.Step(m)
		}
	}
	f.readMessages()
	if !f.logSynced {
		t.Fatalf("logSynced = false")
	}
	if term, _ := f.raftLog.term(4); term != 3 {
		t.Fatalf("follower entry 4 has term %d: the stale tail was truncated", term)
	}

	// Node 1 acknowledges 4/4: the leader commits 4.
	l.Step(pb.Message{From: 1, To: 2, Term: 4, Type: pb.MsgAppResp, Index: 4})
	if l.raftLog.committed != 4 {
		t.Fatalf("leader committed = %d", l.raftLog.committed)
	}
	l.readMessages()

	// The leader's heartbeat carries Commit 4 (#140); the follower commits its 4/3.
	l.bcastHeartbeat()
	for _, m := range l.readMessages() {
		if m.To == 3 && m.Type == pb.MsgHeartbeat {
			f.Step(m)
		}
	}
	lt, _ := l.raftLog.term(4)
	for i := uint64(1); i <= f.raftLog.committed; i++ {
		ft, _ := f.raftLog.term(i)
		lt, _ = l.raftLog.term(i)
		if ft != lt {
			t.Errorf("follower committed entry %d of term %d; the leader's (committed) entry %d has term %d", i, ft, i, lt)
		}
	}
}
