package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A node restarting while in the joint configuration (1 2 3 4)&&(1 2 3), with
// witness 3 in both halves, cannot restore its own ConfState: newRaft panics.
func TestWitnessRestartInJointConfig(t *testing.T) {
	cs := pb.ConfState{
		Voters: []uint64{1, 2, 3, 4}, VotersOutgoing: []uint64{1, 2, 3},
		Witness: 3, WitnessOutgoing: 3,
	}
	s := NewMemoryStorage()
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("newRaft panicked on restart: %v", r)
		}
	}()
	newTestRaft(1, 10, 1, s)
}
