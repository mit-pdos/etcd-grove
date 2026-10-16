// Reproduction for issues/raft-memorystorage-compact-without-snapshot.md (etcd-io/raft#108).
//
// Drop this file into package raft (the repository root) of go.etcd.io/raft/v3 at the
// verified pin, upamanyus/etcd 509271dac (raft v3.7.0 plus the fork's read-index fix), or
// at etcd-io/raft main, and run
//
//	go test -run TestCompactWithoutSnapshotPanics .
//
// MemoryStorage.Compact does not require a prior CreateSnapshot, and Snapshot then returns
// the empty snapshot with a nil error. A leader that has to catch a peer up from below the
// compaction boundary falls back to maybeSendSnapshot, which panics on the empty snapshot.
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestCompactWithoutSnapshotPanics(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2))
	var ents []*pb.Entry
	for i := uint64(1); i <= 10; i++ {
		ents = append(ents, &pb.Entry{Index: new(i), Term: new(uint64(1))})
	}
	if err := s.Append(ents); err != nil {
		t.Fatal(err)
	}
	// Compact without CreateSnapshot: allowed by the API (nothing is applied above 5
	// yet: raft starts with applied = FirstIndex()-1 = 5).
	if err := s.Compact(5); err != nil {
		t.Fatal(err)
	}
	if snap, err := s.Snapshot(); err != nil || !IsEmptySnap(snap) {
		t.Fatalf("expected the empty snapshot and no error, got %v, %v", snap, err)
	}

	r := newTestRaft(1, 10, 1, s)
	r.becomeCandidate()
	r.becomeLeader()
	r.readMessages()

	defer func() {
		p := recover()
		if p == nil {
			t.Fatalf("no panic")
		}
		t.Logf("panic: %v", p)
		if p != "need non-empty snapshot" {
			t.Fatalf("unexpected panic: %v", p)
		}
	}()
	// Peer 2 has nothing: it rejects the probe at the leader's last index with hint 0,
	// so Next drops to 1, below the compaction boundary.
	li := r.raftLog.lastIndex()
	r.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Type: pb.MsgAppResp.Enum(),
		Term: new(r.Term), Index: new(li - 1), Reject: new(true), RejectHint: new(uint64(0))})
}
