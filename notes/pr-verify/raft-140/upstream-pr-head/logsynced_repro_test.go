package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestLogSyncedStaleTail: a follower whose log has an uncommitted tail from an
// older term accepts a MsgApp of the new leader whose entries end before that
// tail. maybeAppend finds no conflict and keeps the tail, yet logSynced becomes
// true, and a heartbeat carrying the leader's commit index then commits the
// stale tail.
//
// Leader 1, term 3: log 1/1 2/1 3/1 3/4 3/5 3/6, committed 6.
// Follower 2:       log 1/1 2/1 3/1 2/4 2/5 2/6 (4..6 from a term-2 leader).
func TestLogSyncedStaleTail(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := storage.Append([]pb.Entry{
		{Index: 1, Term: 1}, {Index: 2, Term: 1}, {Index: 3, Term: 1},
		{Index: 4, Term: 2}, {Index: 5, Term: 2}, {Index: 6, Term: 2},
	}); err != nil {
		t.Fatal(err)
	}
	f := newTestRaft(2, 10, 1, storage)
	f.becomeFollower(3, 1)

	// A MsgApp of term 3 consistent with the leader's log: prev (2, 1), entry 3/1.
	f.Step(pb.Message{From: 1, To: 2, Term: 3, Type: pb.MsgApp, Index: 2, LogTerm: 1,
		Entries: []pb.Entry{{Index: 3, Term: 1}}, Commit: 6})
	if !f.logSynced {
		t.Fatalf("logSynced = false")
	}
	if got := f.raftLog.lastIndex(); got != 6 {
		t.Fatalf("lastIndex = %d: the stale tail was truncated", got)
	}

	// The leader's heartbeat (the PR sends its full commit index).
	f.Step(pb.Message{From: 1, To: 2, Term: 3, Type: pb.MsgHeartbeat, Commit: 6})
	for i := uint64(4); i <= f.raftLog.committed; i++ {
		if term, _ := f.raftLog.term(i); term != 3 {
			t.Errorf("committed entry %d has term %d; the leader's entry %d has term 3", i, term, i)
		}
	}
}
