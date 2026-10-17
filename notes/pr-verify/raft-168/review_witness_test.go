package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestReviewLastEntryAfterSnapshot(t *testing.T) {
	s := NewMemoryStorage()
	cs := pb.ConfState{Voters: []uint64{1, 2, 3}, Witness: 3}
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	defer func() {
		if x := recover(); x != nil {
			t.Fatalf("lastEntry panicked: %v", x)
		}
	}()
	_ = r.raftLog.lastEntry()
}

// candidate restored from a snapshot, gets 1 vote of 2 needed, asks the witness
func TestReviewCandidateAfterSnapshotWitness(t *testing.T) {
	s := NewMemoryStorage()
	cs := pb.ConfState{Voters: []uint64{1, 2, 3}, Witness: 3}
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	defer func() {
		if x := recover(); x != nil {
			t.Fatalf("candidate panicked: %v", x)
		}
	}()
	r.Step(pb.Message{From: 1, To: 1, Type: pb.MsgHup})
	t.Logf("state %v term %d", r.state, r.Term)
	r.Step(pb.Message{From: 1, To: 1, Term: r.Term, Type: pb.MsgVoteResp})
	r.Step(pb.Message{From: 2, To: 1, Term: r.Term, Type: pb.MsgVoteResp, Reject: true})
	t.Logf("state %v witnessMsgs %d cfg %s votes %v", r.state, len(r.witnessMsgs), r.trk.Config, r.trk.Votes)
}

func TestReviewLeaderMaybeCommitCompacted(t *testing.T) {
	s := NewMemoryStorage()
	cs := pb.ConfState{Voters: []uint64{1, 2, 3, 4}, Witness: 4}
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	r.becomeCandidate()
	r.becomeLeader()
	t.Logf("leader %v last %d first %d", r.state, r.raftLog.lastIndex(), r.raftLog.firstIndex())
	r.trk.Progress[3].RecentActive = false
	r.trk.Progress[2].RecentActive = true
	r.trk.Progress[4].RecentActive = true
	t.Logf("changed %v epoch %+v", r.trk.ChangeReplicationSet(), *r.trk.Epoch)
	r.trk.Progress[2].Match = 10
	defer func() {
		if x := recover(); x != nil {
			t.Fatalf("maybeCommit panicked: %v", x)
		}
	}()
	r.maybeCommit()
}
