//go:build ignore

// Requirement snippets for raft's core (batch R2): the Ready phases of rawnode.go.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftcore/ready-advance: Ready, the client's writes, then Advance, whose acknowledgements step
// with no error; a second Ready only after Advance.
// Users: rawnode.go:131-135 (RawNode.Ready), :477-490 (RawNode.Advance); node.go:363, :435-436,
// :443-446.
// Assumes: between Ready and Advance the client enters the batch and does its storage writes
// (R1's readyEnter, readyStor), and applies or skips its conf changes.
// Specs: RawNode.readyWithoutAccept.spec, ready_handout.spec, RawNode.acceptReady.spec,
// rawNodeAt_advance.spec, ackOk_type.spec, raft.Step.spec (StepSrc.ack).
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
// Ready if HasReady is then false. Such a Ready is empty (no soft or hard state, entries, committed
// entries, messages, read states or snapshot): the stale send hands nothing out.
// Users: node.go:353-364 (the loop top), :435 (the send on readyc).
// Assumes: no acceptReady between the computation and HasReady.
// Specs: RawNode.readyWithoutAccept.spec, readyFresh_forget.spec, rawNodeAt_core.spec,
// raft.Step.spec, R1's RawNode.HasReady (false: readyFresh and readyEmpty, requested).
func ReqReadyStale(rn *RawNode, m *pb.Message) {
	rd := rn.readyWithoutAccept()
	_ = rn.raft.Step(m)
	if !rn.HasReady() {
		if rd.SoftState != nil || rd.HardState != nil || len(rd.Entries) != 0 ||
			len(rd.CommittedEntries) != 0 || len(rd.Messages) != 0 || len(rd.ReadStates) != 0 ||
			rd.Snapshot != nil {
			panic("ready-stale: a stale Ready with content")
		}
		rn.acceptReady(rd)
	}
}

// REQ raftcore/ready-peek: node.run reads the raft struct between computing a Ready and handing it
// out; the Ready stays the current one.
// Users: node.go:363 (computed), :367-380 (lead, hasLeader, logger, id, Term), :435-436 (sent,
// accepted).
// Assumes: nothing.
// Specs: RawNode.readyWithoutAccept.spec, readyFresh_ro.spec, raftRO_peek.spec,
// raft.hasLeader.spec, ready_handout.spec, RawNode.acceptReady.spec.
func ReqReadyPeek(rn *RawNode, send func(Ready)) {
	rd := rn.readyWithoutAccept()
	r := rn.raft
	if r.hasLeader() {
		r.logger.Infof("%x leader %x at term %d", r.id, r.lead, r.Term)
	}
	send(rd)
	rn.acceptReady(rd)
}

// REQ raftcore/new-rawnode: NewRawNode's construction around newRaft: the first previous hard state
// is the stored one, and the configuration read back is the one given (but for validate's defaults).
// Users: rawnode.go:51-61.
// Assumes: R1's NewRawNode premises (ConfigOk, a MemoryStorage holding the durable state, ...).
// Specs: newRaft.spec, raft.softState.spec, raft.hardState.spec, raftBoot_bind.spec.
func ReqNewRawNode(c *Config, ms *MemoryStorage) *RawNode {
	c.Storage = ms
	hs, _, _ := ms.InitialState()
	r := newRaft(c)
	rn := &RawNode{raft: r}
	rn.asyncStorageWrites = c.AsyncStorageWrites
	if rn.asyncStorageWrites {
		panic("new-rawnode: asynchronous writes")
	}
	ss := r.softState()
	rn.prevSoftSt = &ss
	rn.prevHardSt = r.hardState()
	if !isHardStateEqual(rn.prevHardSt, hs) || ss.Lead != None || ss.RaftState != StateFollower {
		panic("new-rawnode: not the stored hard state, or not a follower without leader")
	}
	return rn
}

// REQ raftcore/bootstrap: RawNode.Bootstrap on an empty storage: the bootstrap entries appended and
// committed at term 1 and each AddNode applied; the first Ready hands them out.
// Users: bootstrap.go:32-81 (RawNode.Bootstrap), node.go:258 (setupNode for StartNode); etcd's first
// start (server/etcdserver/bootstrap.go:599).
// Assumes: peers non-empty with non-empty contexts (R1's BootLog); the storage empty.
// Specs: R1's RawNode.Bootstrap.spec, rawNodeAt_bootstrap.spec, raft.becomeFollower.spec,
// raft.applyConfChange.spec (committed entries, decided at cluster_alloc).
func ReqBootstrap(rn *RawNode, peers []Peer) {
	if err := rn.Bootstrap(peers); err != nil {
		panic("bootstrap: error")
	}
	if rn.raft.Term != 1 || rn.raft.raftLog.committed != uint64(len(peers)) {
		panic("bootstrap: not at term 1 with the peers committed")
	}
	rd := rn.Ready()
	if len(rd.CommittedEntries) != len(peers) {
		panic("bootstrap: entries not handed out")
	}
}
