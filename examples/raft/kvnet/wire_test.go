package kvnet

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// TestMsgRoundTrip checks that getMsg reads back what putMsg wrote, and refuses its truncations.
func TestMsgRoundTrip(t *testing.T) {
	ents := []*pb.Entry{
		{Term: new(uint64(3)), Index: new(uint64(7)), Type: pb.EntryNormal.Enum(), Data: []byte("op")},
		{Term: new(uint64(3)), Index: new(uint64(8)), Type: pb.EntryConfChangeV2.Enum(), Data: []byte{}},
		// a message's entry of any type reads back, a negative one too
		{Term: new(uint64(3)), Index: new(uint64(9)), Type: pb.EntryType(-5).Enum(), Data: []byte("x")},
		{Term: new(uint64(3)), Index: new(uint64(10)), Type: pb.EntryType(1 << 30).Enum(), Data: []byte{}},
	}
	snap := &pb.Snapshot{Data: []byte("state"), Metadata: &pb.SnapshotMetadata{Index: new(uint64(6)), Term: new(uint64(2)),
		ConfState: &pb.ConfState{Voters: []uint64{1, 2}, Learners: []uint64{3}, VotersOutgoing: []uint64{1},
			LearnersNext: []uint64{4}, AutoLeave: new(true)}}}
	msgs := []*pb.Message{
		{Type: pb.MsgApp.Enum(), To: new(uint64(2)), From: new(uint64(1)), Term: new(uint64(3)), LogTerm: new(uint64(2)),
			Index: new(uint64(6)), Commit: new(uint64(5)), Entries: ents},
		{Type: pb.MsgAppResp.Enum(), To: new(uint64(1)), From: new(uint64(2)), Term: new(uint64(3)), Index: new(uint64(4)),
			Reject: new(true), RejectHint: new(uint64(4)), LogTerm: new(uint64(1)), Entries: []*pb.Entry{}},
		{Type: pb.MsgHeartbeat.Enum(), To: new(uint64(9)), From: new(uint64(1)), Term: new(uint64(3)), Context: []byte("ctx"),
			Entries: []*pb.Entry{}},
		{Type: pb.MsgSnap.Enum(), To: new(uint64(3)), From: new(uint64(1)), Term: new(uint64(3)), Snapshot: snap,
			Entries: []*pb.Entry{}},
	}
	for _, m := range msgs {
		b := putMsg(nil, m)
		got, ok := getMsg(b)
		if !ok {
			t.Fatalf("getMsg refused putMsg(%v)", m)
		}
		// the decoded message sets every field; compare through the getters
		if got.GetType() != m.GetType() || got.GetTo() != m.GetTo() || got.GetFrom() != m.GetFrom() ||
			got.GetTerm() != m.GetTerm() || got.GetLogTerm() != m.GetLogTerm() || got.GetIndex() != m.GetIndex() ||
			got.GetCommit() != m.GetCommit() || got.GetVote() != m.GetVote() || got.GetReject() != m.GetReject() ||
			got.GetRejectHint() != m.GetRejectHint() || string(got.GetContext()) != string(m.GetContext()) ||
			len(got.GetEntries()) != len(m.GetEntries()) || (m.Snapshot == nil) != (got.Snapshot == nil) {
			t.Fatalf("round trip of %v gave %v", m, got)
		}
		for i, e := range m.GetEntries() {
			g := got.GetEntries()[i]
			if g.GetTerm() != e.GetTerm() || g.GetIndex() != e.GetIndex() || g.GetType() != e.GetType() ||
				string(g.GetData()) != string(e.GetData()) {
				t.Fatalf("entry %d: %v, want %v", i, g, e)
			}
		}
		if m.Snapshot != nil && !proto.Equal(got.Snapshot, m.Snapshot) {
			t.Fatalf("snapshot: %v, want %v", got.Snapshot, m.Snapshot)
		}
		for n := 0; n < len(b); n++ {
			if _, ok := getMsg(b[:n]); ok {
				t.Fatalf("getMsg took a truncation of %d bytes of %d", n, len(b))
			}
		}
	}
}

// TestConfChangeRoundTrip checks PutConfChange and GetConfChange.
func TestConfChangeRoundTrip(t *testing.T) {
	ccs := []pb.ConfChangeI{
		&pb.ConfChange{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: new(uint64(3))},
		&pb.ConfChangeV2{},
		&pb.ConfChangeV2{Transition: pb.ConfChangeTransitionJointExplicit.Enum(), Changes: []*pb.ConfChangeSingle{
			{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(4))},
			{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: new(uint64(5))}}},
	}
	for _, cc := range ccs {
		got, ok := GetConfChange(PutConfChange(nil, cc))
		if !ok {
			t.Fatalf("GetConfChange refused PutConfChange(%v)", cc)
		}
		// through the getters (the decoded change sets the transition even when it is Auto: raft
		// reads changes only through getters, LeaveJoint included)
		g, w := got.AsV2(), cc.AsV2()
		if _, v1 := cc.(*pb.ConfChange); v1 != (func() bool { _, ok := got.(*pb.ConfChange); return ok })() ||
			g.GetTransition() != w.GetTransition() || g.LeaveJoint() != w.LeaveJoint() ||
			len(g.GetChanges()) != len(w.GetChanges()) {
			t.Fatalf("round trip of %v gave %v", cc, got)
		}
		for i, c := range w.GetChanges() {
			if g.GetChanges()[i].GetType() != c.GetType() || g.GetChanges()[i].GetNodeId() != c.GetNodeId() {
				t.Fatalf("round trip of %v gave %v", cc, got)
			}
		}
	}
}
