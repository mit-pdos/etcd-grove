package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestCompactWithoutSnapshotPanics: Compact's documentation asks only that the
// compact index be at most raftLog.applied. Compacting a MemoryStorage within that
// bound, but past its snapshot (here: no snapshot at all), makes the leader panic
// with "need non-empty snapshot" when a follower needs a compacted entry.
func TestCompactWithoutSnapshotPanics(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2))
	ents := []*pb.Entry{}
	for i := uint64(1); i <= 5; i++ {
		ents = append(ents, &pb.Entry{Index: new(i), Term: new(uint64(1))})
	}
	if err := s.Append(ents); err != nil {
		t.Fatal(err)
	}
	if err := s.SetHardState(&pb.HardState{Term: new(uint64(1)), Commit: new(uint64(5))}); err != nil {
		t.Fatal(err)
	}
	cfg := newTestConfig(1, 10, 1, s)
	cfg.Applied = 5
	r := newRaft(cfg)
	// Within Compact's documented precondition: 4 <= applied = 5.
	if err := s.Compact(4); err != nil {
		t.Fatal(err)
	}
	r.becomeCandidate()
	r.becomeLeader()
	// Follower 2 lags: its next entry was compacted.
	r.trk.Progress[2].BecomeProbe()
	r.trk.Progress[2].Next = 1
	r.trk.Progress[2].RecentActive = true
	defer func() {
		if p := recover(); p != nil {
			t.Logf("panic: %v", p)
			return
		}
		t.Fatal("expected a panic")
	}()
	r.sendAppend(2)
}
