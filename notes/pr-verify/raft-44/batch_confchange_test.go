package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestStepRefusedConfChangeInBatchLeavesPendingConfIndex: a MsgProp whose
// first entry is an accepted conf change and whose second is refused (the
// first is now pending) is dropped as a whole, with ErrProposalDropped, but
// the first entry already moved pendingConfIndex to an index no entry was
// appended at. Every later conf change is then refused until some other
// entry is appended there and applied: on an idle leader, forever.
func TestStepRefusedConfChangeInBatchLeavesPendingConfIndex(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1)))
	r.becomeCandidate()
	r.becomeLeader()
	// Commit and apply the leader's empty entry.
	r.raftLog.commitTo(r.raftLog.lastIndex())
	r.appliedTo(r.raftLog.committed, 0)
	last := r.raftLog.lastIndex()
	if r.pendingConfIndex > r.raftLog.applied {
		t.Fatalf("setup: pendingConfIndex %d > applied %d", r.pendingConfIndex, r.raftLog.applied)
	}

	cc := func(id uint64) pb.Entry {
		data, err := (&pb.ConfChange{Type: pb.ConfChangeAddNode, NodeID: id}).Marshal()
		if err != nil {
			t.Fatal(err)
		}
		return pb.Entry{Type: pb.EntryConfChange, Data: data}
	}
	err := r.Step(pb.Message{From: 1, To: 1, Type: pb.MsgProp, Entries: []pb.Entry{cc(2), cc(3)}})
	if err != ErrProposalDropped {
		t.Fatalf("batch: err = %v, want ErrProposalDropped", err)
	}
	if got := r.raftLog.lastIndex(); got != last {
		t.Fatalf("batch: lastIndex = %d, want %d (nothing appended)", got, last)
	}
	t.Logf("after the dropped batch: lastIndex %d, applied %d, pendingConfIndex %d",
		r.raftLog.lastIndex(), r.raftLog.applied, r.pendingConfIndex)

	// A single conf change, with every entry applied, is now refused.
	err = r.Step(pb.Message{From: 1, To: 1, Type: pb.MsgProp, Entries: []pb.Entry{cc(2)}})
	if err != nil {
		t.Errorf("single conf change on an applied log: err = %v, want nil (pendingConfIndex %d > lastIndex %d)",
			err, r.pendingConfIndex, r.raftLog.lastIndex())
	}
}
