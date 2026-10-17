// Probes for etcd-io/raft#139 (raft: advance commit index safely), at the PR's head
// 4e08f525c and at its base 026484c68. Run with `go test -run TestProbe -v .` in the
// repository root after copying this file there.
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A storage whose last entry is of a term above the persisted HardState's (here: entries,
// no HardState). At the PR, the log's leaderTerm starts at the last entry's term (3), the
// node campaigns at term 1, and becomeLeader's appendEntry calls raftLog.append(1, ...),
// which returns without appending: the leader's empty entry is silently dropped (and
// appendEntry still reports it accepted). At the base the entry is appended.
func TestProbeLeaderEmptyEntryDropped(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1))
	if err := storage.Append([]pb.Entry{{Index: 1, Term: 3}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, storage)
	r.becomeCandidate()
	r.becomeLeader()
	t.Logf("term=%d lastIndex=%d lastTerm=%d", r.Term, r.raftLog.lastIndex(), r.raftLog.lastTerm())
	if r.raftLog.lastIndex() != 2 {
		t.Errorf("the new leader's empty entry was not appended: lastIndex = %d, want 2",
			r.raftLog.lastIndex())
	}
}

// A MsgApp whose entries are of a term above the message's: the PR's append panics
// ("leader at term 2 tries to append a higher term 3"); the base appends them.
func TestProbeMsgAppEntryAboveMsgTerm(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1, 2))
	r := newTestRaft(1, 10, 1, storage)
	r.becomeFollower(2, 2)
	defer func() {
		if p := recover(); p != nil {
			t.Errorf("panic: %v", p)
		}
	}()
	r.Step(pb.Message{From: 2, To: 1, Type: pb.MsgApp, Term: 2, LogTerm: 0, Index: 0,
		Entries: []pb.Entry{{Index: 1, Term: 3}}})
	t.Logf("lastIndex=%d", r.raftLog.lastIndex())
}

// A snapshot whose last entry the follower's log already has, from a leader of a term the
// log's leaderTerm is not at: the PR skips the fast-forward of the commit index (and replies
// with the old commit index); the base commits up to the snapshot's index.
func TestProbeSnapshotFastForwardSkipped(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1, 2))
	if err := storage.Append([]pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 2}, {Index: 3, Term: 2}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, storage)
	r.becomeFollower(3, 2)
	r.Step(pb.Message{From: 2, To: 1, Type: pb.MsgSnap, Term: 3, Snapshot: &pb.Snapshot{
		Metadata: pb.SnapshotMetadata{Index: 2, Term: 2, ConfState: pb.ConfState{Voters: []uint64{1, 2}}}}})
	msgs := r.readMessages()
	t.Logf("committed=%d replies=%v", r.raftLog.committed, msgs)
	if r.raftLog.committed != 2 {
		t.Errorf("committed = %d, want 2 (the snapshot's index)", r.raftLog.committed)
	}
}
