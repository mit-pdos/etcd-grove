//go:build ignore

// Requirement snippets for raft's core (batch R2): what node.run and RawNode read directly.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftcore/status: the status getters give the node's id and fresh memory.
// Users: rawnode.go:493-496 (Status), :500-502 (BasicStatus), node.go:447-448 (run's status arm).
// Assumes: nothing.
// Specs: getStatus.spec, getBasicStatus.spec.
func ReqStatus(r *raft) {
	s := getStatus(r)
	if s.ID != r.id {
		panic("status: wrong id")
	}
	if getBasicStatus(r).ID != r.id {
		panic("status: wrong id")
	}
}

// REQ raftcore/fields: node.run's direct reads of the raft struct and its filter of responses
// from unknown peers.
// Users: node.go:349-381 (lead, Term, id, logger, hasLeader), :395 (trk.Progress).
// Assumes: m is a well-formed message (msgPts) of a type in range, 0 <= type (IsResponseMsg
// indexes a table by it; a received message has one by msgSent_type).
// Specs: raftRO_peek.spec, raft.hasLeader.spec.
func ReqFields(r *raft, m *pb.Message) bool {
	if r.hasLeader() != (r.lead != None) {
		panic("fields: hasLeader")
	}
	r.logger.Infof("%x at term %d", r.id, r.Term)
	return IsResponseMsg(m.GetType()) && r.trk.Progress[m.GetFrom()] == nil
}

// REQ raftcore/tick-missed: node.Tick, from any goroutine, reads the raft struct's id and logger
// while run owns the struct, when the tick channel is full.
// Users: node.go:456-465 (node.Tick's default case).
// Assumes: nothing (the fields are never written after newRaft).
// Specs: raftRO_peek.spec (id, logger: persistent shares the node's invariant keeps).
func ReqTickMissed(r *raft) {
	r.logger.Warningf("%x A tick missed to fire. Node blocks too long!", r.id)
}

// REQ raftcore/logger: a logger set for the package is what a Config without one gets.
// Users: etcd's newRaftNode (raft.SetLogger with its zap adapter); Config.validate.
// Assumes: l meets raft's Logger contract (loggerOk).
// Specs: SetLogger.spec, getLogger.spec, loggerOk_nonnil.spec; raft_init.spec (raftLoggerMu's lock
// invariant: the package logger meets loggerOk).
func ReqLogger(l Logger) {
	SetLogger(l)
	if getLogger() == nil {
		panic("logger: nil")
	}
}
