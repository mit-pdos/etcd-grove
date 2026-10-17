package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestReview47MsgAppEntryTermAboveMsgTerm: a follower at term 2 accepts a MsgApp of term 2 whose
// entry has term 5 (no correct leader sends it; handleAppendEntries never calls logSlice.valid).
// Its log's last term (5) is then above its term; on its next won election becomeLeader's
// appendEntry panics with raft#47 (without it, it appends an entry of term 3 after one of term 5).
func TestReview47MsgAppEntryTermAboveMsgTerm(t *testing.T) {
	sm := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1)))
	sm.becomeFollower(2, 2)
	sm.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Type: pb.MsgApp.Enum(),
		Term: new(uint64(2)), LogTerm: new(uint64(0)), Index: new(uint64(0)),
		Entries: []*pb.Entry{{Index: new(uint64(1)), Term: new(uint64(5))}}})
	t.Logf("after MsgApp: term %d, last entry %+v", sm.Term, sm.raftLog.lastEntryID())
	var p any
	func() {
		defer func() { p = recover() }()
		sm.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgHup.Enum()})
		for _, m := range sm.msgsAfterAppend {
			if m.GetTo() == 1 {
				sm.Step(m)
			}
		}
	}()
	t.Logf("state %v term %d panic %v", sm.state, sm.Term, p)
	if p == nil {
		var terms []uint64
		for i := uint64(1); i <= sm.raftLog.lastIndex(); i++ {
			terms = append(terms, mustTerm(sm.raftLog.term(i)))
		}
		t.Logf("no panic, log terms %v", terms)
	}
}
