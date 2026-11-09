//go:build ignore

// Requirement snippets for raft's core (batch R2): what node.run and RawNode read directly.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftcore/status: the status getters give the node's id and fresh memory.
// Users: rawnode.go:460 (Status), :466 (BasicStatus), node.go:425 (run's status arm).
// Assumes: nothing.
// Specs: getStatus.spec, getBasicStatus.spec.
func ReqStatus(r *raft) {
	s := getStatus(r)
	if s.ID != r.id {
		panic("status: wrong id")
	}
	s.HardState.Term = new(uint64(0)) // fresh: the caller may write it
	if getBasicStatus(r).ID != r.id {
		panic("status: wrong id")
	}
}

// REQ raftcore/fields: node.run's direct reads of the raft struct and its filter of responses
// from unknown peers.
// Users: node.go:349-381 (lead, Term, id, logger, hasLeader), :391 (trk.Progress).
// Assumes: nothing.
// Specs: raftCore_peek.spec, raft.hasLeader.spec.
func ReqFields(r *raft, m *pb.Message) bool {
	if r.hasLeader() != (r.lead != None) {
		panic("fields: hasLeader")
	}
	r.logger.Infof("%x at term %d", r.id, r.Term)
	return IsResponseMsg(m.GetType()) && r.trk.Progress[m.GetFrom()] == nil
}

// REQ raftcore/logger: a logger set for the package is what a Config without one gets.
// Users: etcd's newRaftNode (raft.SetLogger with its zap adapter); Config.validate.
// Assumes: l meets raft's Logger contract (loggerOk).
// Specs: SetLogger.spec, getLogger.spec.
func ReqLogger(l Logger) {
	SetLogger(l)
	if getLogger() == nil {
		panic("logger: nil")
	}
}
