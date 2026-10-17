package raft

import (
	"reflect"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestProgressCommitAboveLeaderCommit shows that the Progress.Commit invariants
// documented by etcd-io/raft#132 ("Commit <= leader's commit index",
// "sentCommit >= Commit") do not hold: a follower that learned a higher commit
// index from the previous leader reports it to a new leader that has not
// committed that far yet.
func TestProgressCommitAboveLeaderCommit(t *testing.T) {
	ids := []uint64{1, 2, 3, 4, 5}
	rs := map[uint64]*raft{}
	for _, id := range ids {
		rs[id] = newTestRaft(id, 10, 1, newTestMemoryStorage(withPeers(ids...)))
	}
	// deliver routes messages until quiescence; keep decides which are delivered.
	deliver := func(keep func(m pb.Message) bool) {
		for {
			var msgs []pb.Message
			for _, id := range ids {
				msgs = append(msgs, rs[id].readMessages()...)
			}
			if len(msgs) == 0 {
				return
			}
			for _, m := range msgs {
				if keep(m) {
					_ = rs[m.To].Step(m)
				}
			}
		}
	}
	all := func(pb.Message) bool { return true }

	// 1 becomes leader of term 1 and commits its empty entry everywhere.
	rs[1].becomeCandidate()
	rs[1].becomeLeader()
	deliver(all)
	// 1 replicates a proposal (index 2) to everyone and commits it, but the
	// commit index 2 reaches only 3: every message from 1 after the
	// MsgAppResps carrying index 2 is dropped except those to 3.
	rs[1].Step(pb.Message{From: 1, To: 1, Type: pb.MsgProp, Entries: []pb.Entry{{Data: []byte("x")}}})
	for _, m := range rs[1].readMessages() {
		rs[m.To].Step(m)
	}
	for _, id := range []uint64{2, 3, 4, 5} {
		for _, m := range rs[id].readMessages() {
			rs[m.To].Step(m)
		}
	}
	if rs[1].raftLog.committed != 2 {
		t.Fatalf("leader 1 committed %d, want 2", rs[1].raftLog.committed)
	}
	for _, m := range rs[1].readMessages() {
		if m.To == 3 {
			rs[3].Step(m)
		}
	}
	// Drop 3's responses.
	for _, id := range ids {
		rs[id].readMessages()
	}
	if rs[3].raftLog.committed != 2 || rs[2].raftLog.committed >= 2 {
		t.Fatalf("committed: 3 at %d, 2 at %d", rs[3].raftLog.committed, rs[2].raftLog.committed)
	}

	// 2 (log up to date, commit below 2) wins term 2 with the votes of 3, 4 and 5.
	rs[2].becomeCandidate()
	rs[2].becomeLeader()
	rs[2].bcastAppend()
	if rs[2].raftLog.committed >= 2 {
		t.Fatalf("new leader committed %d", rs[2].raftLog.committed)
	}
	// Its MsgApp reaches 3 only, and 3's response comes back.
	t.Logf("2: last=%d committed=%d; 3: last=%d committed=%d", rs[2].raftLog.lastIndex(), rs[2].raftLog.committed, rs[3].raftLog.lastIndex(), rs[3].raftLog.committed)
	for _, m := range rs[2].readMessages() {
		t.Logf("2 sends %+v", m)
		if m.To == 3 {
			rs[3].Step(m)
		}
	}
	for _, m := range rs[3].readMessages() {
		t.Logf("3 sends %+v", m)
		if m.To == 2 {
			rs[2].Step(m)
		}
	}
	pr := rs[2].trk.Progress[3]
	sent := reflect.ValueOf(pr).Elem().FieldByName("sentCommit").Uint()
	t.Logf("leader 2: committed=%d; progress of 3: %s sentCommit=%d", rs[2].raftLog.committed, pr, sent)
	if pr.Commit > rs[2].raftLog.committed {
		t.Errorf("Invariant \"Commit <= leader's commit index\" violated: Commit=%d > committed=%d", pr.Commit, rs[2].raftLog.committed)
	}
	if sent < pr.Commit {
		t.Errorf("Invariant \"sentCommit >= Commit\" violated: sentCommit=%d < Commit=%d", sent, pr.Commit)
	}
}
