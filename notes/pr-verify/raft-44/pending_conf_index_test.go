package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

func ccEntryForTest(t *testing.T, id uint64, ctx []byte) *pb.Entry {
	data, err := proto.Marshal(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx})
	if err != nil {
		t.Fatal(err)
	}
	return &pb.Entry{Type: pb.EntryConfChange.Enum(), Data: data}
}

func propForTest(ents ...*pb.Entry) *pb.Message {
	return &pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgProp.Enum(), Entries: ents}
}

// commitApplyAllForTest commits and applies the whole log of a leader (as if
// every peer had acknowledged it), releasing the uncommitted-size budget.
func commitApplyAllForTest(r *raft) {
	r.raftLog.commitTo(r.raftLog.lastIndex())
	r.reduceUncommittedSize(r.uncommittedSize)
	r.appliedTo(r.raftLog.committed, 0)
}

// TestConfChangeDroppedBySizeLeavesPendingConfIndex: a conf change that the
// conf-change loop accepts but appendEntry then drops (the uncommitted-size
// limit) has already moved pendingConfIndex to lastIndex()+1, where no entry
// was appended. With the whole log applied, the next conf change is refused.
// On the pinned code the refusal turns it into an empty entry (which fills that
// index, so a later retry works); with etcd-io/raft#44 the refusal drops it,
// and every retry is dropped until some other proposal fills the index.
func TestConfChangeDroppedBySizeLeavesPendingConfIndex(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	r.maxUncommittedSize = 100
	r.becomeCandidate()
	r.becomeLeader()
	commitApplyAllForTest(r)

	// Some uncommitted payload, so that the size limit applies.
	if err := r.Step(propForTest(&pb.Entry{Data: make([]byte, 50)})); err != nil {
		t.Fatal(err)
	}
	last := r.raftLog.lastIndex()
	err := r.Step(propForTest(ccEntryForTest(t, 2, make([]byte, 100))))
	if err != ErrProposalDropped {
		t.Fatalf("big conf change: err = %v, want ErrProposalDropped", err)
	}
	t.Logf("after the size drop: lastIndex %d, pendingConfIndex %d", r.raftLog.lastIndex(), r.pendingConfIndex)
	if r.pendingConfIndex > r.raftLog.lastIndex() {
		t.Errorf("pendingConfIndex %d > lastIndex %d: it names an index with no conf change", r.pendingConfIndex, last)
	}

	commitApplyAllForTest(r)
	for try := 1; try <= 3; try++ {
		before := r.raftLog.lastIndex()
		err := r.Step(propForTest(ccEntryForTest(t, 2, nil)))
		ents, _ := r.raftLog.entries(before+1, noLimit)
		t.Logf("retry %d (log applied to %d = lastIndex %d): err %v, appended %d entries", try, r.raftLog.applied, before, err, len(ents))
		if err == nil && len(ents) == 1 && ents[0].GetType() == pb.EntryConfChange {
			return
		}
		commitApplyAllForTest(r)
	}
	t.Errorf("no retry of the conf change on a fully applied, idle leader was appended")
}

// TestStepRefusedConfChangeInBatch: a MsgProp of two conf changes, the second
// refused because the first is now pending. With etcd-io/raft#44 the batch is
// dropped as a whole (ErrProposalDropped), but the first conf change already
// moved pendingConfIndex: the leader then refuses every conf change until some
// other entry fills that index and is applied. (On the pinned code the second
// is replaced by an empty entry and both are appended.)
func TestStepRefusedConfChangeInBatch(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1)))
	r.becomeCandidate()
	r.becomeLeader()
	commitApplyAllForTest(r)
	last := r.raftLog.lastIndex()

	err := r.Step(propForTest(ccEntryForTest(t, 2, nil), ccEntryForTest(t, 3, nil)))
	t.Logf("batch: err %v, lastIndex %d -> %d, pendingConfIndex %d", err, last, r.raftLog.lastIndex(), r.pendingConfIndex)
	if r.pendingConfIndex > r.raftLog.lastIndex() {
		t.Errorf("pendingConfIndex %d > lastIndex %d", r.pendingConfIndex, r.raftLog.lastIndex())
	}
	commitApplyAllForTest(r)
	if err := r.Step(propForTest(ccEntryForTest(t, 2, nil))); err != nil {
		t.Errorf("single conf change on a fully applied log: err %v", err)
	}
}
