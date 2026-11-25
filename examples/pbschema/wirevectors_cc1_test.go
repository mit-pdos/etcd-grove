package pbschema

// The protobuf trust boundary for raftpb's legacy ConfChange (2026-11-24, the trace check's bootstrap
// log; the sibling of stage S1's ConfChangeV2, mit-pdos/etcd-grove#37): the evidence that the Lean wire
// codecs `cc1EncRaw` and `cc1DecodeRaw` (Proof/go_etcd_io/raft/v3/PbWireRaft.lean) are protobuf-go's.
// Since then `ccDecodeV1` (CCModel.lean) is `cc1DecodeRaw`, so the trusted specs of proto.Marshal and
// proto.Unmarshal at *pb.ConfChange (MarshalConfChange, UnmarshalConfChange, and pbutil's
// MustUnmarshalMessage) claim that protobuf-go v1.36.12 (examples/go.mod's pin) computes it; the
// encoder is what the bootstrap log's bytes are written with (`ccBootWire`).
//
// TestConfChangeWireVectors builds the vectors from protobuf-go (a fixed seed) and compares them with
// the Lean module ConfChangeWireVectors.lean, whose #guards check the Lean functions against every
// vector when it is built; WIREVECTORS_UPDATE=1 rewrites the module instead.
//
//   - encode: proto.Marshal of the conf changes raft's Bootstrap builds (ConfChange{Type: AddNode,
//     NodeId: id}, Context nil, empty or not, for ids 1..5 and extreme ones), and of random
//     ConfChanges (each field present or not, zero values, enums out of range, nil, empty and long
//     contexts, unknown fields as the decoder leaves them), checked here to decode back and to have
//     proto.Size's length;
//   - decode: proto.Unmarshal's outcome (the four getters, or an error) on those encodings, on
//     random record sequences (non-minimal tags and varints, repeated scalars, wrong wire types,
//     unknown fields valid or not), on byte mutations of all of them, and on edge cases (enums
//     sign-extended and above 2^32, last-one-wins, truncated and huge lengths, 10- and 11-byte
//     varints, end-group tags, field number 0).

import (
	"bytes"
	"fmt"
	"math"
	"math/rand"
	"strings"
	"testing"

	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

const cc1VectorsPath = "../../Proof/google_golang_org/protobuf/proto/ConfChangeWireVectors.lean"

var cc1Sch = map[int]fdesc{1: {k: kU64}, 2: {k: kEnum}, 3: {k: kU64}, 4: {k: kBytes}}

func randCC1(r *rand.Rand) *pb.ConfChange {
	c := &pb.ConfChange{}
	if r.Intn(2) == 0 {
		v := randU64(r)
		c.Id = &v
	}
	if r.Intn(4) != 0 {
		t := pb.ConfChangeType(randEnum(r))
		c.Type = &t
	}
	if r.Intn(4) != 0 {
		v := randU64(r)
		c.NodeId = &v
	}
	c.Context = randData(r)
	if r.Intn(3) == 0 {
		setUF(c, genUF(r, cc1Sch, validUF))
	}
	return c
}

func cc1EncGuard(c *pb.ConfChange, b []byte) string {
	typ := "none"
	if c.Type != nil {
		typ = fmt.Sprintf("(some %d)", uint32(*c.Type))
	}
	ctx := "none"
	if c.Context != nil {
		ctx = fmt.Sprintf("(some %s)", lh(c.Context))
	}
	return fmt.Sprintf("#guard cc1EncRaw %s %s %s %s %s = %s", optU64(c.Id), typ, optU64(c.NodeId), ctx,
		lh(c.ProtoReflect().GetUnknown()), lh(b))
}

func cc1DecGuard(b []byte) string {
	var c pb.ConfChange
	if err := proto.Unmarshal(b, &c); err != nil {
		return fmt.Sprintf("#guard cc1DecodeRaw %s = none", lh(b))
	}
	return fmt.Sprintf("#guard cc1DecodeRaw %s = some (%d, %d, %d, %s)", lh(b), c.GetId(),
		uint32(c.GetType()), c.GetNodeId(), lh(c.GetContext()))
}

// a random sequence of ConfChange records, valid or not.
func randCC1Records(r *rand.Rand) []byte {
	var b []byte
	for k := r.Intn(6); k > 0; k-- {
		switch r.Intn(5) {
		case 0, 1:
			b = tagPad(b, 1+r.Intn(3), 0, rpad(r))
			b = appendVarintPad(b, rval(r), rpad(r))
		case 2:
			b = append(b, lenRec(4, randData(r))...)
		case 3:
			b = append(b, genUF(r, cc1Sch, badUF)...)
		default:
			b = append(b, genUnknownField(r, 1+r.Intn(5), rwt(r), 0, r.Intn(2) == 0)...)
		}
	}
	return b
}

func buildCC1Vectors(t *testing.T) string {
	r := rand.New(rand.NewSource(3701))
	var out []string
	var pool [][]byte
	enc := func(c *pb.ConfChange) {
		b, err := proto.Marshal(c)
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if proto.Size(c) != len(b) {
			t.Fatalf("Size %d != len %d", proto.Size(c), len(b))
		}
		var d pb.ConfChange
		if err := proto.Unmarshal(b, &d); err != nil || d.GetId() != c.GetId() || d.GetType() != c.GetType() ||
			d.GetNodeId() != c.GetNodeId() || !bytes.Equal(d.GetContext(), c.GetContext()) ||
			!bytes.Equal(d.ProtoReflect().GetUnknown(), c.ProtoReflect().GetUnknown()) {
			t.Fatalf("round trip of %v: %v (%v)", c, &d, err)
		}
		out = append(out, cc1EncGuard(c, b))
		pool = append(pool, b)
	}

	out = append(out, "/-! ## `ConfChange`: `proto.Marshal` of `Bootstrap`'s conf changes -/", "")
	// raft's Bootstrap (bootstrap.go): ConfChange{Type: ConfChangeAddNode.Enum(), NodeId: &peer.ID,
	// Context: peer.Context}
	for _, id := range []uint64{1, 2, 3, 4, 5, 127, 128, 1 << 32, math.MaxUint64} {
		for _, ctx := range [][]byte{nil, {}, []byte("ctx")} {
			v := id
			c := &pb.ConfChange{Type: pb.ConfChangeType_ConfChangeAddNode.Enum(), NodeId: &v, Context: ctx}
			enc(c)
		}
	}

	out = append(out, "", "/-! ## `ConfChange`: `proto.Marshal` -/", "")
	for i := 0; i < 100; i++ {
		enc(randCC1(r))
	}

	out = append(out, "", "/-! ## `ConfChange`: `proto.Unmarshal` -/", "")
	var ins [][]byte
	ins = append(ins, pool...)
	for i := 0; i < 100; i++ {
		ins = append(ins, randCC1Records(r))
	}
	base := append([][]byte(nil), ins...)
	for i := 0; i < 200; i++ {
		ins = append(ins, mutateW(r, base[r.Intn(len(base))], base))
	}
	ten := func(last byte) []byte { return append(bytes.Repeat([]byte{0xff}, 9), last) }
	ins = append(ins,
		[]byte{},
		cat(tagB(2, 0), ten(0x01)),                            // Type -1 (sign-extended)
		cat(tagB(2, 0), []byte{0x80, 0x80, 0x80, 0x80, 0x10}), // Type 2^32: the low bits 0
		cat(tagB(1, 0), ten(0x01)),                            // Id 2^64 - 1
		cat(tagB(1, 0), ten(0x02)),                            // overflow
		cat(tagB(3, 0), ten(0x81), []byte{0x00}),              // 11 bytes
		cat(varRec(3, 1), varRec(3, 2)),                       // last one wins
		cat(lenRec(4, []byte{1}), lenRec(4, nil)),             // Context: last one wins
		cat(tagB(4, 2), []byte{0x05, 0x01}),                   // Context truncated
		cat(tagB(4, 2), ten(0x01)),                            // huge length
		varRec(4, 1),                                          // Context with the wrong wire type: unknown
		lenRec(3, []byte{1}),                                  // NodeId with the wrong wire type: unknown
		[]byte{0x00},                                          // number 0
		[]byte{0x18},                                          // NodeId without a value
		tagB(5, 4),                                            // end group at the top
		cat([]byte{0x98, 0x00}, []byte{0x05}),                 // non-minimal tag of NodeId
	)
	for _, b := range ins {
		out = append(out, cc1DecGuard(b))
	}
	return strings.Join(out, "\n")
}

func TestConfChangeWireVectors(t *testing.T) {
	hdr := `/-
**The wire codecs' vectors: ` + "`raftpb.ConfChange`" + `** (protobuf trust boundary, 2026-11-24; the sibling of stage
S1's ` + "`ConfChangeV2`" + `, mit-pdos/etcd-grove#37): protobuf-go v1.36.12's ` + "`proto.Marshal`" + ` and
` + "`proto.Unmarshal`" + ` of ` + "`raftpb.ConfChange`" + `, checked by ` + "`#guard`" + ` against the Lean codecs ` + "`cc1EncRaw`" + ` and
` + "`cc1DecodeRaw`" + ` (` + "`Proof/go_etcd_io/raft/v3/PbWireRaft.lean`" + `), the latter of which ` + "`ccDecodeV1`" + ` is.
GENERATED by ` + "`examples/pbschema/wirevectors_cc1_test.go`" + ` (` + "`TestConfChangeWireVectors`" + `, which fails if this
file is not what it generates): do not edit; rerun
` + "`cd examples && WIREVECTORS_UPDATE=1 GOWORK=off go test -run '^TestConfChangeWireVectors$' ./pbschema/`" + `.
-/
module

public import Proof.go_etcd_io.raft.v3.PbWireRaft
-- the #guards run the codecs at elaboration time
public meta import Proof.go_etcd_io.raft.v3.PbWireRaft

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace CC1WireVectors

open Wire

` + vectorsHelpers
	text := hdr + buildCC1Vectors(t) + "\n\nend CC1WireVectors\nend EtcdGrove\nend Perennial\n"
	checkOrWrite(t, cc1VectorsPath, text)
}

var _ = protowire.AppendTag
