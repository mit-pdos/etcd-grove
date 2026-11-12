// Package confstate checks the conf state's unknown fields (premise fixes 1, fix 5, 2026-11-10):
// raft's csPts (Proof/go_etcd_io/raft/v3/InvPb.lean) said a conf state has none, and it is reached
// by proto.UnmarshalPb at pbMessage (a decoded *raftpb.Message, msgPtsC → snapshot → metadata →
// conf state), but a MsgSnap whose ConfState carries an unknown field decodes and keeps it; then
// proto.Equal against a conf state of the same model is false, and raft's Equivalent errors
// (assertConfStatesEquivalent panicked: nonissues/raft-confstate-unknown-fields-panic.md, fixed in
// the raft fork by premise fixes 2: Equivalent compares the configurations).
// Found by etcd-grove-81's independent review (/shared/tmp/pfix-review/t/review_test.go).
package confstate

import (
	"bytes"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
)

func mustM(t *testing.T, m proto.Message) []byte {
	t.Helper()
	d, err := proto.Marshal(m)
	if err != nil {
		t.Fatal(err)
	}
	return d
}

func TestDecodedMessageConfStateUnknown(t *testing.T) {
	cs := &pb.ConfState{Voters: []uint64{1}, AutoLeave: proto.Bool(false)}
	m := &pb.Message{Type: pb.MsgSnap.Enum(), To: proto.Uint64(2), From: proto.Uint64(1), Term: proto.Uint64(5),
		Snapshot: &pb.Snapshot{Metadata: &pb.SnapshotMetadata{ConfState: cs, Index: proto.Uint64(10), Term: proto.Uint64(5)}}}
	uf := protowire.AppendVarint(protowire.AppendTag(nil, 99, protowire.VarintType), 1)
	cs.ProtoReflect().SetUnknown(uf)
	bs := mustM(t, m) // the bytes arriving at the receiver
	var a pb.Message
	if err := proto.Unmarshal(bs, &a); err != nil {
		t.Fatalf("expected the message to decode: %v", err)
	}
	acs := a.GetSnapshot().GetMetadata().GetConfState()
	if got := acs.ProtoReflect().GetUnknown(); !bytes.Equal(got, uf) {
		t.Fatalf("expected the decoded conf state to keep the unknown field %x, got %x", uf, got)
	}
	fresh := &pb.ConfState{Voters: []uint64{1}, AutoLeave: proto.Bool(false)}
	if proto.Equal(proto.Clone(acs), fresh) {
		t.Fatalf("expected proto.Equal to see the unknown field")
	}
	// Since the raft fork's fourth fix (premise fixes 2), Equivalent compares the configurations,
	// so the unknown field no longer makes the decoded conf state inequivalent (until then it did,
	// and assertConfStatesEquivalent panicked).
	if err := acs.Equivalent(fresh); err != nil {
		t.Fatalf("expected Equivalent to ignore the unknown field, got %v", err)
	}
}
