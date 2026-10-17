package raft

import (
	"bytes"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

func rvCC(t *testing.T, id uint64) *pb.Entry {
	data, err := proto.Marshal(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id)})
	if err != nil {
		t.Fatal(err)
	}
	return &pb.Entry{Type: pb.EntryConfChange.Enum(), Data: data}
}

func rvLeave(t *testing.T) *pb.Entry {
	data, err := proto.Marshal(&pb.ConfChangeV2{})
	if err != nil {
		t.Fatal(err)
	}
	return &pb.Entry{Type: pb.EntryConfChangeV2.Enum(), Data: data}
}

func rvProp(from uint64, ents ...*pb.Entry) *pb.Message {
	return &pb.Message{From: new(from), To: new(from), Type: pb.MsgProp.Enum(), Entries: ents}
}

func rvApplyAll(r *raft) {
	r.raftLog.commitTo(r.raftLog.lastIndex())
	r.reduceUncommittedSize(r.uncommittedSize)
	r.appliedTo(r.raftLog.committed, 0)
}

// An explicit joint configuration: a batch [leave-joint, add] has its leave
// accepted (pendingConfIndex moved) and its add refused, so the batch is
// dropped. The leader then refuses every leave-joint request, staying in the
// joint configuration, until some other entry fills the dangling index.
func TestReviewJointLeaveStallsAfterRefusedBatch(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1)))
	r.becomeCandidate()
	r.becomeLeader()
	rvApplyAll(r)
	r.applyConfChange(&pb.ConfChangeV2{
		Transition: pb.ConfChangeTransitionJointExplicit.Enum(),
		Changes:    []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))}},
	})
	if len(r.trk.Config.Voters[1]) == 0 {
		t.Fatal("not joint")
	}
	err := r.Step(rvProp(1, rvLeave(t), rvCC(t, 3)))
	t.Logf("batch [leave, add 3]: err %v, lastIndex %d, pendingConfIndex %d", err, r.raftLog.lastIndex(), r.pendingConfIndex)
	for try := 1; try <= 3; try++ {
		rvApplyAll(r)
		before := r.raftLog.lastIndex()
		err := r.Step(rvProp(1, rvLeave(t)))
		t.Logf("leave retry %d (applied %d = lastIndex %d): err %v, lastIndex now %d", try, r.raftLog.applied, before, err, r.raftLog.lastIndex())
		if err == nil {
			return
		}
	}
	t.Errorf("leader cannot leave the joint configuration on an idle, fully applied log")
}

// A follower forwards a batch [normal, conf change] while the leader has an
// unapplied conf change: the follower's Step returns nil, and the leader drops
// the whole batch, normal entry included, with nobody told. (Before the PR the
// normal entry was appended and only the conf change emptied.)
func TestReviewForwardedBatchNormalEntryLost(t *testing.T) {
	nt := newNetwork(nil, nil, nil)
	nt.send(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgHup.Enum()})
	lead := nt.peers[1].(*raft)
	if lead.state != StateLeader {
		t.Fatal("1 not leader")
	}
	// A conf change at the leader: committed by the network, never applied.
	nt.send(rvProp(1, rvCC(t, 4)))
	t.Logf("leader: applied %d, pendingConfIndex %d, lastIndex %d", lead.raftLog.applied, lead.pendingConfIndex, lead.raftLog.lastIndex())

	f := nt.peers[2].(*raft)
	payload := []byte("important-normal-entry")
	err := f.Step(rvProp(2, &pb.Entry{Data: payload}, rvCC(t, 5)))
	t.Logf("follower Step of [normal, cc]: err %v", err)
	before := lead.raftLog.lastIndex()
	nt.send(f.readMessages()...)
	ents, _ := lead.raftLog.entries(lead.raftLog.firstIndex(), noLimit)
	found := false
	for _, e := range ents {
		if bytes.Equal(e.GetData(), payload) {
			found = true
		}
	}
	t.Logf("leader lastIndex %d -> %d, normal entry in log: %v", before, lead.raftLog.lastIndex(), found)
	if err == nil && !found {
		t.Errorf("follower's Step returned nil but its normal entry was dropped by the leader")
	}
}
