//go:build ignore

// Requirement snippets for raft's log (batch R3): a received snapshot.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftlog/restore: a follower that receives a snapshot past its commit index restarts its log
// at it: committed at its index, the snapshot pending (handed out by the next Ready), no
// committed entries to apply until it is stored, its last entry the snapshot's.
// Users: raft.go:1870-1945 (handleSnapshot, restore).
// Assumes: s is valid (msgSent of the MsgSnap: snapValid); s.index > committed and its id is
// not in the log (else raft fast-forwards with commitTo); s.index + 1 < 2^64.
// Specs: raftLog.matchTerm.spec, raftLog.commitTo.spec, raftLog.restore.spec,
// raftLog.lastEntryID.spec, raftLog.hasNextUnstableSnapshot.spec, raftLog.nextCommittedEnts.spec.
func ReqRestore(l *raftLog, s *pb.Snapshot) bool {
	idx, term := s.GetMetadata().GetIndex(), s.GetMetadata().GetTerm()
	if idx <= l.committed {
		return false
	}
	if l.matchTerm(entryID{term: term, index: idx}) {
		l.commitTo(idx)
		return false
	}
	l.restore(s)
	if l.committed != idx {
		panic("restore: not committed at the snapshot")
	}
	if last := l.lastEntryID(); last.index != idx || last.term != term {
		panic("restore: last entry is not the snapshot's")
	}
	if !l.hasNextUnstableSnapshot() || len(l.nextCommittedEnts(true)) != 0 {
		panic("restore: snapshot not pending")
	}
	return true
}
