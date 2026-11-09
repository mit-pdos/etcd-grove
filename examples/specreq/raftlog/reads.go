//go:build ignore

// Requirement snippets for raft's log (batch R3): reads for sends, the compaction errors, scans.
package raft

import (
	"errors"

	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftlog/send-or-snapshot: to send to a follower at next, the leader reads the previous
// term and the entries from next; if either is compacted, the snapshot it sends instead is
// non-empty (and valid); a temporarily unavailable snapshot is retried later.
// Users: raft.go:620-690 (maybeSendAppend, maybeSendSnapshot).
// Assumes: 1 <= next <= lastIndex()+1; the log is attached (logStorage); the log fits in memory
// (lastIndex()+1-next < 2^63).
// Specs: raftLog.term.spec, raftLog.entries.spec, raftLog.snapshot.spec, payloadsSize.spec;
// laws: logPersistent.spec (logCompactedLb).
func ReqSendOrSnapshot(l *raftLog, next uint64, maxSize entryEncodingSize) {
	prevTerm, errt := l.term(next - 1)
	ents, erre := l.entries(next, maxSize)
	if errt == nil && erre == nil {
		if next <= l.lastIndex() && len(ents) == 0 {
			panic("send: nothing to send below the last index")
		}
		_ = prevTerm
		_ = payloadsSize(ents)
		return
	}
	snap, err := l.snapshot()
	if err != nil {
		if errors.Is(err, ErrSnapshotTemporarilyUnavailable) {
			return
		}
		panic(err)
	}
	if IsEmptySnap(snap) {
		panic("need non-empty snapshot")
	}
}

// REQ raftlog/conflict-hint: the probing hint is at most the index probed, and every entry
// between it and the probe has a larger term.
// Users: raft.go:1519 (stepLeader's MsgAppResp reject), raft.go:1839 (handleAppendEntries).
// Specs: raftLog.findConflictByTerm.spec, raftLog.term.spec.
func ReqConflictHint(l *raftLog, index, term uint64) {
	hint, hintTerm := l.findConflictByTerm(index, term)
	if hint > index {
		panic("conflict-hint: past the probe")
	}
	if hintTerm > term {
		panic("conflict-hint: term too large")
	}
	for j := hint + 1; j <= index; j++ {
		if t, err := l.term(j); err != nil || t <= term {
			panic("conflict-hint: skipped a candidate")
		}
	}
}

// REQ raftlog/prev-term: the term of the last entry is always known; terms of indices past the
// last index are unavailable, never wrong.
// Users: raft.go:625 (sendAppend), raft.go:2070 (committedEntryInCurrentTerm).
// Specs: raftLog.lastEntryID.spec, raftLog.term.spec, raftLog.zeroTermOnOutOfBounds.spec.
func ReqPrevTerm(l *raftLog) {
	last := l.lastEntryID()
	if t, err := l.term(last.index); err != nil || t != last.term {
		panic("prev-term: last term unknown")
	}
	if last.index < ^uint64(0) {
		if _, err := l.term(last.index + 1); !errors.Is(err, ErrUnavailable) {
			panic("prev-term: a term past the end")
		}
	}
	_ = l.zeroTermOnOutOfBounds(l.term(l.committed))
}

// REQ raftlog/scan-conf-changes: the unapplied committed entries are visited in order, each page
// once, and a callback's error stops the scan with that error.
// Users: raft.go:1014-1040 (hasUnappliedConfChanges).
// Assumes: applied >= the log's base (outside appliedSnap); the range fits in memory.
// Specs: raftLog.scan.spec.
func ReqScanConfChanges(l *raftLog) bool {
	if l.applied >= l.committed {
		return false
	}
	found := false
	errBreak := errors.New("break")
	next := l.applied + 1
	err := l.scan(l.applied+1, l.committed+1, l.maxApplyingEntsSize, func(ents []*pb.Entry) error {
		for _, e := range ents {
			if e.GetIndex() != next {
				panic("scan: out of order")
			}
			next++
			if e.GetType() == pb.EntryConfChange || e.GetType() == pb.EntryConfChangeV2 {
				found = true
				return errBreak
			}
		}
		return nil
	})
	if err != nil && err != errBreak {
		panic("scan: unexpected error")
	}
	if err == nil && next != l.committed+1 {
		panic("scan: range not covered")
	}
	return found
}
