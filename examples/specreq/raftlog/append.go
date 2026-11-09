//go:build ignore

// Requirement snippets for raft's log (batch R3): appends and commits. The log's types are
// unexported, so these compile only inside package raft (go.etcd.io/raft/v3); they are kept
// gofmt-clean and checked by reading against the specs in Spec/go_etcd_io/raft/v3/raftLog__*.lean.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftlog/start: a log over a storage starts committed and applied at the storage's
// compaction point, with every stored entry stable and nothing unstable; its last entry's term
// is known.
// Users: raft.go:443 (newRaft: newLogWithSize, then InitialState, lastEntryID, loadState).
// Assumes: maxSize > 0 (ConfigOk: MaxSizePerMsg or MaxCommittedSizePerReady non-zero, and
// validate copies the former into the latter); the storage is attached to nothing else yet; its
// last index + 1 < 2^64 and its compaction point at most its snapshot's index (StorageHolds).
// Specs: newLogWithSize.spec, raftLog_borrowStarting.spec, raftLog.lastEntryID.spec,
// raftLog.firstIndex.spec, raftLog.lastIndex.spec; laws: raftLog_fields.spec, logFresh_attach.spec.
func ReqStart(st Storage, lg Logger, maxSize entryEncodingSize) *raftLog {
	l := newLogWithSize(st, lg, maxSize)
	hs, _, err := st.InitialState()
	if err != nil {
		panic("InitialState failed")
	}
	fi, _ := st.FirstIndex()
	li, _ := st.LastIndex()
	if l.committed != fi-1 || l.applied != fi-1 || l.lastIndex() != li {
		panic("start: wrong committed/applied/last")
	}
	if l.hasNextUnstableEnts() || l.hasNextOrInProgressSnapshot() {
		panic("start: something unstable")
	}
	_ = l.lastEntryID() // no panic: the last term is known
	if c := hs.GetCommit(); c > l.committed && c <= l.lastIndex() {
		l.committed = c // loadState
	}
	return l
}

// REQ raftlog/leader-append: the leader's proposals are appended after its last index, and the
// new last index covers them; the leader commits an entry of its term that a quorum matched.
// Users: raft.go:831-852 (appendEntry), raft.go:796 (maybeCommit).
// Assumes: ents are the leader's, at indices li+1, ..., of term `term` (non-zero), a fresh slice
// with no spare capacity (appendEntry's clone); li+len(ents) < 2^64; no snapshot pending (a leader
// is promotable).
// Specs: raftLog.lastIndex.spec, raftLog.append.spec, raftLog.maybeCommit.spec, raftLog.term.spec.
func ReqLeaderAppend(l *raftLog, term uint64, ents []*pb.Entry) {
	li := l.lastIndex()
	if len(ents) == 0 {
		return
	}
	if got := l.append(ents...); got != li+uint64(len(ents)) {
		panic("leader-append: wrong last index")
	}
	if t, err := l.term(li + 1); err != nil || t != term {
		panic("leader-append: appended entry not found")
	}
	if l.maybeCommit(entryID{term: term, index: li + 1}) && l.committed != li+1 {
		panic("leader-append: commit did not move")
	}
}

// REQ raftlog/follower-append: a follower appends a leader's entries after a matching prev (and
// rejects otherwise, unchanged); after it, the log has every entry and commits up to the leader's
// commit within them.
// Users: raft.go:1809-1851 (handleAppendEntries, handleHeartbeat's commitTo).
// Assumes: a.prev.index >= committed (the early return before it); the cluster's log matching:
// past a matching prev, the leader's entries agree with the committed prefix; a.entries are at
// indices a.prev.index+1, ... (the MsgApp's), with no spare capacity (a decoded message).
// Specs: raftLog.maybeAppend.spec, raftLog.matchTerm.spec, raftLog.commitTo.spec,
// raftLog.findConflictByTerm.spec, raftLog.lastIndex.spec.
func ReqFollowerAppend(l *raftLog, a logSlice, leaderCommit uint64) {
	if a.prev.index < l.committed {
		return
	}
	oldCommitted := l.committed
	last, ok := l.maybeAppend(a, leaderCommit)
	if !ok {
		if l.committed != oldCommitted {
			panic("follower-append: a rejected append changed the log")
		}
		hint := min(a.prev.index, l.lastIndex())
		if idx, _ := l.findConflictByTerm(hint, a.prev.term); idx > hint {
			panic("follower-append: hint past the probe")
		}
		return
	}
	if last != a.prev.index+uint64(len(a.entries)) {
		panic("follower-append: wrong last new index")
	}
	for _, e := range a.entries {
		if !l.matchTerm(pbEntryID(e)) {
			panic("follower-append: entry missing after append")
		}
	}
	if l.committed < min(leaderCommit, last) && l.committed < oldCommitted {
		panic("follower-append: commit went backwards")
	}
}
