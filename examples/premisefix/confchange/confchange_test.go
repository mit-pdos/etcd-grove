// Package confchange checks what proto.Marshal of a raft *pb.ConfChange depends on (premise fixes
// 1, 2026-11-10): the boot entry's bytes depend on field presence and on the unknown fields, which
// raft's ConfChangeM forgets (bootMarshal, Proof/go_etcd_io/raft/v3/ApiVocab.lean); and the round
// trip of proto.MarshalConfChange.wp_proof (Spec/google_golang_org/protobuf/proto/MarshalConfChange.lean)
// fails for arbitrary unknown-field bytes but holds for those proto.Unmarshal leaves.
package confchange

import (
	"bytes"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

func marshal(t *testing.T, cc *pb.ConfChange) []byte {
	t.Helper()
	d, err := proto.Marshal(cc)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	return d
}

func decode(t *testing.T, d []byte) *pb.ConfChange {
	t.Helper()
	var back pb.ConfChange
	if err := proto.Unmarshal(d, &back); err != nil {
		t.Fatalf("Unmarshal: %v", err)
	}
	return &back
}

func sameModel(a, b *pb.ConfChange) bool {
	return a.GetType() == b.GetType() && a.GetNodeId() == b.GetNodeId() && a.GetId() == b.GetId() &&
		bytes.Equal(a.GetContext(), b.GetContext())
}

// raft's Bootstrap builds &pb.ConfChange{Type: AddNode.Enum(), NodeId: new(id), Context: ctx}
// (bootstrap.go): the same ConfChangeM with another presence pattern or unknown fields marshals
// to other bytes, so bootMarshal holds only of the objects Bootstrap builds.
func TestBootBytesDependOnPresence(t *testing.T) {
	id := uint64(0x136af3ff76043cae)
	ctx := []byte(`{"id":1399198912774159534,"peerURLs":["http://127.0.0.1:23800"],"name":"putget"}`)
	boot := marshal(t, &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx})
	z := uint64(0)
	idZero := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx, Id: &z}
	typeNil := &pb.ConfChange{NodeId: new(id), Context: ctx}
	unknown := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: ctx}
	unknown.ProtoReflect().SetUnknown([]byte{0x28, 0x01}) // field 5, varint 1
	for name, cc := range map[string]*pb.ConfChange{"Id=&0": idZero, "Type=nil": typeNil, "unknown field 5": unknown} {
		d := marshal(t, cc)
		if !sameModel(decode(t, d), decode(t, boot)) {
			t.Fatalf("%s: not the boot conf change's model", name)
		}
		if bytes.Equal(d, boot) {
			t.Fatalf("%s: expected bytes other than the boot entry's", name)
		}
		t.Logf("%s: %d bytes, boot entry %d bytes", name, len(d), len(boot))
	}
	// Context: an empty non-nil slice is present (proto2 bytes), a nil one is not.
	e := marshal(t, &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id), Context: []byte{}})
	n := marshal(t, &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id)})
	t.Logf("Context []byte{}: %d bytes, nil: %d bytes", len(e), len(n))
}

// The round trip of proto.MarshalConfChange.wp_proof, for arbitrary unknown fields: false (an
// unknown-field record with node_id's number and wire type overrides NodeId; garbage bytes do
// not decode).
func TestRoundTripArbitraryUnknownFails(t *testing.T) {
	cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(7))}
	cc.ProtoReflect().SetUnknown([]byte{0x18, 0x09}) // field 3 (node_id), varint 9
	if got := decode(t, marshal(t, cc)).GetNodeId(); got != 9 {
		t.Fatalf("expected the unknown field to override NodeId, got %d", got)
	}
	cc.ProtoReflect().SetUnknown([]byte{0xff})
	var back pb.ConfChange
	if err := proto.Unmarshal(marshal(t, cc), &back); err == nil {
		t.Fatalf("expected garbage unknown fields not to decode")
	}
}

// For the unknown fields proto.Unmarshal leaves (records of unknown numbers, and known numbers at
// the wrong wire type), the round trip holds: re-marshaling and decoding gives the same fields.
func TestRoundTripUnmarshalLeftovers(t *testing.T) {
	src := marshal(t, &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(7)), Context: []byte("c")})
	src = append(src, 0x28, 0x01)       // field 5 (unknown), varint 1
	src = append(src, 0x1a, 0x01, 0x09) // field 3 (node_id) at wire type 2 (bytes): unknown
	cc := decode(t, src)
	if len(cc.ProtoReflect().GetUnknown()) == 0 {
		t.Fatalf("expected unknown fields")
	}
	back := decode(t, marshal(t, cc))
	if !sameModel(back, cc) || back.GetNodeId() != 7 {
		t.Fatalf("round trip changed the fields: %v vs %v", back, cc)
	}
}
