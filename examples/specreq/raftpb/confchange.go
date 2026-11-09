package raftpb

import (
	"bytes"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// REQ raftpb/marshal-decode: a change built by a client marshals without error, with the entry type
// of its kind, and its bytes unmarshal (into the type the entry type names) to the same change:
// raft's apply (and etcd's) decodes every committed conf entry.
// Users: node.go:489 (ProposeConfChange), raft.go:1332/1338 (stepLeader's pending check),
// etcd server.go (applyConfChange), raft doc.go:137 (the documented apply loop).
// Assumes: the change's context is below 2^40 bytes (wireBound).
// Specs: MarshalConfChange.spec (decodeConfChange of the bytes), proto's Unmarshal.spec,
// confChangeV1Pts_msgAt.spec, ConfChange.GetNodeId.spec.
func ReqMarshalDecode(id uint64, ctx []byte) {
	cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx}
	typ, data, err := pb.MarshalConfChange(cc)
	if err != nil || typ != pb.EntryConfChange {
		panic("marshal")
	}
	var dec pb.ConfChange
	if err := proto.Unmarshal(data, &dec); err != nil {
		panic("decode")
	}
	if dec.GetNodeId() != id || dec.GetType() != pb.ConfChangeAddNode || !bytes.Equal(dec.GetContext(), ctx) {
		panic("decoded another change")
	}
}

// REQ raftpb/auto-leave: MarshalConfChange(nil) is an EntryConfChangeV2 with no data, which decodes
// to the empty ConfChangeV2: a change that leaves the joint configuration.
// Users: raft.go appliedTo (the leader's auto-leave proposal), raft.go:1346 (wantsLeaveJoint).
// Specs: MarshalConfChange.spec (o = none), proto's Unmarshal.spec, ConfChangeV2.LeaveJoint.spec.
func ReqAutoLeave() {
	typ, data, err := pb.MarshalConfChange(nil)
	if err != nil || typ != pb.EntryConfChangeV2 || len(data) != 0 {
		panic("auto-leave entry")
	}
	var cc pb.ConfChangeV2
	if err := proto.Unmarshal(data, &cc); err != nil {
		panic("decode empty")
	}
	if !cc.LeaveJoint() {
		panic("empty change does not leave")
	}
}

// REQ raftpb/asv2: a legacy change's V2 form is one change of the same type and node, transition
// Auto, so it is applied as a simple change (not joint).
// Users: rawnode.go:112, node.go:565 (ApplyConfChange), bootstrap.go:79, util.go:216.
// Specs: ConfChange.AsV2.spec, ConfChangeV2.LeaveJoint.spec, ConfChangeV2.EnterJoint.spec,
// ConfChangeV2.GetChanges.spec, ConfChangeSingle.GetNodeId.spec.
func ReqAsV2(id uint64) {
	cc := &pb.ConfChange{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: new(id)}
	v2 := cc.AsV2()
	if v2.LeaveJoint() {
		panic("a removal leaves")
	}
	if _, joint := v2.EnterJoint(); joint {
		panic("one change enters joint")
	}
	if len(v2.GetChanges()) != 1 || v2.GetChanges()[0].GetNodeId() != id {
		panic("AsV2 changed the change")
	}
}

// REQ raftpb/enter-leave: EnterJoint and LeaveJoint as raft dispatches on them (several changes or
// an explicit transition enter a joint configuration, auto-leaving unless JointExplicit).
// Users: raft.go:1947-1963 (applyConfChange), examples/specreq/raftconf (validConf).
// Assumes: the transition is one of the three known ones (EnterJoint panics otherwise).
// Specs: ConfChangeV2.EnterJoint.spec, ConfChangeV2.LeaveJoint.spec, ConfChangeTransition.Enum.spec.
func ReqEnterLeave(a, b uint64) {
	cc := &pb.ConfChangeV2{
		Transition: pb.ConfChangeTransitionJointExplicit.Enum(),
		Changes: []*pb.ConfChangeSingle{
			{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(a)},
			{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: new(b)},
		},
	}
	autoLeave, ok := cc.EnterJoint()
	if !ok || autoLeave || cc.LeaveJoint() {
		panic("explicit joint")
	}
}

// REQ raftpb/equivalent: two ConfStates listing the same ids in other orders are Equivalent, and
// neither is changed (raft's assertConfStatesEquivalent panics on an error).
// Users: raft util.go:321 (assertConfStatesEquivalent, from newRaft and appliedSnap).
// Specs: ConfState.Equivalent.spec, ConfState.GetVoters.spec.
func ReqEquivalent() {
	cs1 := &pb.ConfState{Voters: []uint64{1, 2, 3}, Learners: []uint64{5}}
	cs2 := &pb.ConfState{Voters: []uint64{3, 1, 2}, Learners: []uint64{5}, AutoLeave: new(false)}
	if err := cs1.Equivalent(cs2); err != nil {
		panic(err)
	}
	if cs1.GetVoters()[0] != 1 || cs2.GetVoters()[0] != 3 {
		panic("Equivalent sorted its arguments")
	}
	cs3 := &pb.ConfState{Voters: []uint64{1, 2}}
	if cs1.Equivalent(cs3) == nil {
		panic("different configurations equivalent")
	}
}
