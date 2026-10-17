// Review probes for etcd-io/raft#139. Copy into the repository root (package raft) and run
// `go test -run TestReview -v .` at the PR head and at its base.
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// A follower whose log already contains the leader's snapshot's last entry, with a stale
// uncommitted tail and a commit index below the snapshot's, and whose log's leaderTerm is
// older than the leader's term (it has not accepted an append from this leader yet). The
// leader (log compacted) sends it a snapshot. At the PR the follower skips the fast-forward
// commit and answers MsgAppResp{Index: old commit}, which does not move the leader's
// progress out of StateSnapshot: without a ReportSnapshot from the application, the leader
// never sends this follower anything again and its commit index never advances. At the base
// the answer carries the snapshot's index and the leader resumes replication.
func TestReviewSnapFastForwardStall(t *testing.T) {
	// Leader: snapshot (2, 2), term 3 persisted; it will campaign at 4.
	s1 := NewMemoryStorage()
	if err := s1.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 2, Term: 2,
		ConfState: pb.ConfState{Voters: []uint64{1, 2}}}}); err != nil {
		t.Fatal(err)
	}
	if err := s1.SetHardState(pb.HardState{Term: 3, Commit: 2}); err != nil {
		t.Fatal(err)
	}
	// Follower: 1@1 2@2 3@2 (3@2 a stale entry the new leader does not have), commit 1.
	s2 := newTestMemoryStorage(withPeers(1, 2))
	if err := s2.Append([]pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 2}, {Index: 3, Term: 2}}); err != nil {
		t.Fatal(err)
	}
	if err := s2.SetHardState(pb.HardState{Term: 3, Commit: 1}); err != nil {
		t.Fatal(err)
	}
	r1 := newTestRaft(1, 10, 1, s1)
	r2 := newTestRaft(2, 10, 1, s2)
	nt := newNetwork(r1, r2)
	r1.becomeCandidate()
	r1.becomeLeader()
	r1.readMessages()
	// The leader probes the follower below its compaction point (e.g. after a low rejection
	// hint): it has to send a snapshot.
	pr := r1.trk.Progress[2]
	pr.Next = 2
	r1.maybeSendAppend(2, true)
	nt.send(r1.readMessages()...)
	t.Logf("after MsgSnap: follower committed=%d, leader's progress of 2: %v", r2.raftLog.committed, pr)
	// Keep the cluster busy: proposals and heartbeats.
	for i := 0; i < 5; i++ {
		nt.send(pb.Message{From: 1, To: 1, Type: pb.MsgProp, Entries: []pb.Entry{{Data: []byte("x")}}})
		nt.send(pb.Message{From: 1, To: 1, Type: pb.MsgBeat})
	}
	t.Logf("after traffic: follower committed=%d lastIndex=%d, leader committed=%d lastIndex=%d, progress %v",
		r2.raftLog.committed, r2.raftLog.lastIndex(), r1.raftLog.committed, r1.raftLog.lastIndex(), pr)
	if pr.State == tracker.StateSnapshot {
		t.Errorf("the leader's progress of the follower is stuck in StateSnapshot")
	}
	if r2.raftLog.committed < 2 {
		t.Errorf("the follower's commit index is stuck at %d", r2.raftLog.committed)
	}
	// With the application's ReportSnapshot it recovers.
	nt.send(pb.Message{From: 2, To: 1, Type: pb.MsgSnapStatus})
	nt.send(pb.Message{From: 1, To: 1, Type: pb.MsgBeat})
	t.Logf("after MsgSnapStatus: follower committed=%d lastIndex=%d, progress %v",
		r2.raftLog.committed, r2.raftLog.lastIndex(), pr)
}

// A follower that already has every entry of a new leader's appends (no conflict) but whose
// log's leaderTerm is older: the PR does not commit even what the append proves committed.
// (The new leader's own entry at its term eventually conflicts and unblocks it.)
func TestReviewNoConflictAppendNoCommit(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2))
	if err := s.Append([]pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 2}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	r.becomeFollower(3, 2)
	r.Step(pb.Message{From: 2, To: 1, Type: pb.MsgApp, Term: 3, LogTerm: 1, Index: 1, Commit: 2,
		Entries: []pb.Entry{{Index: 2, Term: 2}}})
	t.Logf("committed=%d leaderTerm(PR only)", r.raftLog.committed)
	if r.raftLog.committed != 2 {
		t.Errorf("committed = %d, want 2", r.raftLog.committed)
	}
}
