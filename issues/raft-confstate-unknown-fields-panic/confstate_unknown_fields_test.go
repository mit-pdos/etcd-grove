package raft

import (
	"testing"

	"google.golang.org/protobuf/encoding/protowire"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A snapshot whose ConfState carries an unknown field (one a newer version of raftpb
// added) makes the follower that restores it panic in assertConfStatesEquivalent:
// Equivalent compares with proto.Equal, which compares unknown fields, and the ConfState
// raft builds from its tracker has none.
func TestSnapshotConfStateUnknownFieldPanics(t *testing.T) {
	cs := &pb.ConfState{Voters: []uint64{1, 2}}
	unknown := protowire.AppendVarint(protowire.AppendTag(nil, 99, protowire.VarintType), 1)
	cs.ProtoReflect().SetUnknown(unknown)
	snap := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index: new(uint64(11)), Term: new(uint64(11)), ConfState: cs}}

	// Equivalent alone: the same configuration is reported as not equivalent.
	if err := cs.Equivalent(&pb.ConfState{Voters: []uint64{1, 2}}); err == nil {
		t.Fatalf("Equivalent ignored the unknown field")
	}

	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	defer func() {
		if p := recover(); p == nil {
			t.Fatalf("restore did not panic")
		} else {
			t.Logf("panic: %v", p)
		}
	}()
	r.Step(&pb.Message{Type: pb.MsgSnap.Enum(), From: new(uint64(2)), To: new(uint64(1)),
		Term: new(uint64(2)), Snapshot: snap})
}
