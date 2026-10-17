package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A follower whose storage lost the tail of what it acknowledged (the case the
// change targets: writes acknowledged before they were durable) can come back with
// entries of an older term at indices the leader has since committed with other
// entries. A heartbeat carries no term check of the follower's log, so clamping the
// commit index to lastIndex commits (and hands to the application) entries that are
// not the cluster's committed entries.
func TestCommitToClampCommitsDivergentEntries(t *testing.T) {
	// The follower's surviving log: entries 1..3 of term 1 (an old leader's).
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s.Append([]pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 1, Data: []byte("old-2")}, {Index: 3, Term: 1, Data: []byte("old-3")}}); err != nil {
		t.Fatal(err)
	}
	if err := s.SetHardState(pb.HardState{Term: 1, Commit: 1}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(2, 10, 1, s)
	// The leader of term 2 committed 1..5, its entries 2..5 of term 2, counting this
	// follower's (since lost) acknowledgement of index 5; it heartbeats commit 5.
	r.Step(pb.Message{From: 1, To: 2, Type: pb.MsgHeartbeat, Term: 2, Commit: 5})
	if r.raftLog.committed != 3 {
		t.Fatalf("committed = %d, want 3 (clamped)", r.raftLog.committed)
	}
	ents := r.raftLog.nextCommittedEnts(true)
	for _, e := range ents {
		if e.Index >= 2 && e.Term != 2 {
			t.Errorf("follower applies entry %d of term %d (%q); the leader's committed entry %d is of term 2", e.Index, e.Term, e.Data, e.Index)
		}
	}
}


// After the clamp the follower holds entries 2..3 of term 1 as committed, and the
// leader cannot repair them: an MsgApp below the follower's commit index is answered
// with that index as a success, and one at or above it does not match. The follower
// stays divergent while acknowledging the leader's heartbeats.
func TestCommitToClampNeverRepaired(t *testing.T) {
	// The leader: entry 1 of term 1, then 2..5 of term 2, all committed.
	s1 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s1.Append([]pb.Entry{{Index: 1, Term: 1}}); err != nil {
		t.Fatal(err)
	}
	if err := s1.SetHardState(pb.HardState{Term: 1, Commit: 1}); err != nil {
		t.Fatal(err)
	}
	r1 := newTestRaft(1, 10, 1, s1)
	r1.becomeCandidate() // term 2
	r1.becomeLeader()    // empty entry 2 of term 2
	mustAppendEntry(r1, pb.Entry{Data: []byte("new-3")}, pb.Entry{Data: []byte("new-4")}, pb.Entry{Data: []byte("new-5")})
	nextEnts(r1, s1)
	r1.raftLog.commitTo(5)
	// Follower 2 acknowledged 1..5 of term 2 (pr.Match = 5), then lost those writes.
	pr := r1.prs.Progress[2]
	pr.Match, pr.Next = 5, 6
	pr.BecomeReplicate()
	r1.readMessages()

	s2 := newTestMemoryStorage(withPeers(1, 2, 3))
	if err := s2.Append([]pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 1}, {Index: 3, Term: 1}}); err != nil {
		t.Fatal(err)
	}
	if err := s2.SetHardState(pb.HardState{Term: 1, Commit: 1}); err != nil {
		t.Fatal(err)
	}
	r2 := newTestRaft(2, 10, 1, s2)

	for round := 0; round < 50; round++ {
		r1.Step(pb.Message{From: 1, To: 1, Type: pb.MsgBeat})
		mustAppendEntry(r1, pb.Entry{Data: []byte("more")})
		for i := 0; i < 10; i++ {
			for _, m := range r1.readMessages() {
				if m.To == 2 {
					r2.Step(m)
				}
			}
			nextEnts(r1, s1)
			nextEnts(r2, s2)
			for _, m := range r2.readMessages() {
				if m.To == 1 {
					r1.Step(m)
				}
			}
		}
	}
	for i := uint64(2); i <= 3; i++ {
		t1, _ := r1.raftLog.term(i)
		t2, _ := r2.raftLog.term(i)
		if t1 != t2 {
			t.Errorf("after 50 rounds, entry %d: leader term %d, follower term %d (follower committed %d, last %d)",
				i, t1, t2, r2.raftLog.committed, r2.raftLog.lastIndex())
		}
	}
}
