//go:build ignore

// Requirement snippets for raft's core (batch R2): the sources of a step and its only error.
// Package raft: the calls are to unexported functions (node.go's and rawnode.go's uses).
package raft

import (
	"errors"

	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftcore/step-received: a received message steps without panic; only a forwarded proposal
// may be refused, with ErrProposalDropped.
// Users: node.go:392 (run's recvc arm), rawnode.go:140 (RawNode.Step).
// Assumes: m was sent by a node of the cluster to r's node (msgSent, its credit, To = id).
// Specs: raft.Step.spec (stepIn's first case).
func ReqStepReceived(r *raft, m *pb.Message) {
	if err := r.Step(m); err != nil {
		if m.GetType() != pb.MsgProp || !errors.Is(err, ErrProposalDropped) {
			panic("step-received: unexpected error")
		}
	}
}

// REQ raftcore/step-propose: a local proposal is appended, forwarded or dropped
// (ErrProposalDropped), never another error.
// Users: node.go:384 (run's propc arm, From set to the node's id), rawnode.go:85 (Propose).
// Assumes: the client's update for the entry (propUpd).
// Specs: raft.Step.spec (stepIn's proposal case).
func ReqStepPropose(r *raft, data []byte) {
	err := r.Step(&pb.Message{Type: pb.MsgProp.Enum(), From: new(r.id), Entries: []*pb.Entry{{Data: data}}})
	if err != nil && !errors.Is(err, ErrProposalDropped) {
		panic("step-propose: unexpected error")
	}
}

// REQ raftcore/step-read: a local read request steps with no error.
// Users: rawnode.go:521 (ReadIndex), node.go:392 (node.ReadIndex through recvc).
// Assumes: rctx is a registered read context (readCtx).
// Specs: raft.Step.spec (stepIn's read case).
func ReqStepRead(r *raft, rctx []byte) {
	if err := r.Step(&pb.Message{Type: pb.MsgReadIndex.Enum(), Entries: []*pb.Entry{{Data: rctx}}}); err != nil {
		panic("step-read: error")
	}
}

// REQ raftcore/step-reports: the node API's local reports and campaigns step with no error, at any
// role (follower, candidate, leader, learner, removed).
// Users: rawnode.go:96 (Campaign), :494 (ReportUnreachable), :501 (ReportSnapshot),
// :507 (TransferLeader), :513 (ForgetLeader); node.go's same through recvc.
// Assumes: nothing.
// Specs: raft.Step.spec (stepIn's report case).
func ReqStepReports(r *raft, peer uint64) {
	ms := []*pb.Message{
		{Type: pb.MsgHup.Enum()},
		{Type: pb.MsgUnreachable.Enum(), From: new(peer)},
		{Type: pb.MsgSnapStatus.Enum(), From: new(peer), Reject: new(true)},
		{Type: pb.MsgTransferLeader.Enum(), From: new(peer)},
		{Type: pb.MsgForgetLeader.Enum()},
	}
	for _, m := range ms {
		if err := r.Step(m); err != nil {
			panic("step-reports: error")
		}
	}
}

// REQ raftcore/tick: a tick, through the field, at any role.
// Users: rawnode.go:73 (RawNode.Tick), node.go:416 (run's tickc arm).
// Assumes: nothing (the term never wraps: receipts, ApiCore.lean).
// Specs: raftCore_peek.spec (r.tick), raft.tickElection.spec, raft.tickHeartbeat.spec.
func ReqTick(r *raft, n int) {
	for i := 0; i < n; i++ {
		r.tick()
	}
}
