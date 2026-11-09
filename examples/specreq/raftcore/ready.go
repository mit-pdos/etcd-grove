//go:build ignore

// Requirement snippets for raft's core (batch R2): the Ready phases of rawnode.go.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftcore/ready-advance: Ready, the client's writes, then Advance, whose acknowledgements step
// with no error; a second Ready only after Advance.
// Users: rawnode.go:165 (RawNode.Ready), :451 (RawNode.Advance); node.go:363, :419, :425.
// Assumes: between Ready and Advance the client enters the batch and does its storage writes
// (R1's readyEnter, readyStor), and applies or skips its conf changes.
// Specs: RawNode.readyWithoutAccept.spec, ready_handout.spec, RawNode.acceptReady.spec,
// rawNodeAt_advance.spec, raft.Step.spec (StepSrc.ack).
func ReqReadyAdvance(rn *RawNode, write func(Ready)) {
	rd := rn.readyWithoutAccept()
	rn.acceptReady(rd)
	write(rd)
	for i, m := range rn.stepsOnAdvance {
		if err := rn.raft.Step(m); err != nil {
			panic("ready-advance: acknowledgement refused")
		}
		rn.stepsOnAdvance[i] = nil
	}
	rn.stepsOnAdvance = rn.stepsOnAdvance[:0]
	rd2 := rn.readyWithoutAccept()
	rn.acceptReady(rd2) // would panic ("two accepted Ready structs") without the loop above
}

// REQ raftcore/ready-stale: node.run computes a Ready, steps other messages, and sends the old
// Ready if HasReady is then false. That Ready is still the current one but for its soft state:
// no entries, committed entries, messages, read states, snapshot or hard state.
// Users: node.go:353-363 (the loop top), :417 (the send on readyc).
// Assumes: no acceptReady between the computation and HasReady.
// Specs: RawNode.readyWithoutAccept.spec, readyFresh_forget.spec, rawNodeAt_core.spec,
// raft.Step.spec, R1's RawNode.HasReady (requested: false gives readyFresh back).
func ReqReadyStale(rn *RawNode, m *pb.Message) {
	rd := rn.readyWithoutAccept()
	_ = rn.raft.Step(m)
	if !rn.HasReady() {
		if len(rd.Entries) != 0 || len(rd.CommittedEntries) != 0 || len(rd.Messages) != 0 ||
			len(rd.ReadStates) != 0 || rd.Snapshot != nil || rd.HardState != nil {
			panic("ready-stale: a stale Ready with content")
		}
		rn.acceptReady(rd)
	}
}

// REQ raftcore/new-rawnode: NewRawNode's construction around newRaft: the first previous hard state
// is the stored one.
// Users: rawnode.go:64.
// Assumes: R1's NewRawNode premises (ConfigOk, a MemoryStorage holding the durable state, ...).
// Specs: newRaft.spec, raft.softState.spec, raft.hardState.spec, raftBoot_bind.spec.
func ReqNewRawNode(c *Config, ms *MemoryStorage) *RawNode {
	c.Storage = ms
	hs, _, _ := ms.InitialState()
	r := newRaft(c)
	rn := &RawNode{raft: r}
	ss := r.softState()
	rn.prevSoftSt = &ss
	rn.prevHardSt = r.hardState()
	if !isHardStateEqual(rn.prevHardSt, hs) || ss.Lead != None || ss.RaftState != StateFollower {
		panic("new-rawnode: not the stored hard state, or not a follower without leader")
	}
	return rn
}
