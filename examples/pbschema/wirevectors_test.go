package pbschema

// The protobuf trust boundary's stage S1 (mit-pdos/etcd-grove#37): the evidence that the Lean wire
// codecs `entryEncRaw`, `entDecodeRaw` and `cc2DecodeRaw` (Proof/go_etcd_io/raft/v3/PbWireRaft.lean,
// over Proof/google_golang_org/protobuf/proto/Wire.lean) are protobuf-go's: since S1, `entryEncC`,
// `entDecode` and `ccDecodeV2` are these functions, so the trusted specs of proto.Marshal and
// proto.Unmarshal (MarshalPb, UnmarshalPb, MarshalConfChangeV2, UnmarshalConfChangeV2) claim that
// protobuf-go v1.36.12 (examples/go.mod's pin) computes them byte for byte.
//
// TestWireVectors builds the vectors from protobuf-go (a fixed seed) and compares them with the Lean
// module EntryWireVectors.lean, whose #guards check the Lean functions against every vector when it
// is built; WIREVECTORS_UPDATE=1 rewrites the module instead.
//
//   - encode: proto.Marshal of random Entries (each field present or not, zero values, negative
//     and large enum values, nil, empty and long Data) with unknown fields as the decoder leaves
//     them (genUF), checked here to decode back (getters and GetUnknown) and to have proto.Size's
//     length;
//   - decode, Entry: proto.Unmarshal's outcome (the getters and the unknown fields, or an error)
//     on those encodings, on valid encodings with unknown fields interleaved and repeated fields
//     (encodeWithUF), on adversarial ones (genAdv, genUF with bad numbers, wire types, ends and
//     non-minimal tags), on byte mutations of all of them (flip, truncate, insert, drop, splice),
//     and on edge cases (10-byte varints, the 10th byte 1 and 2, 11-byte varints, numbers 0, 2^29-1,
//     2^29, 2^31-1, 2^31 inside a group, wire types 4, 6, 7, groups nested 10001 and 10002 deep);
//   - decode, ConfChangeV2: proto.Marshal of random ConfChangeV2s (changes with unknown fields of
//     their own) and proto.Unmarshal's outcome (the getters, or an error) on those encodings, on
//     random record sequences (changes valid or not, repeated scalars), and on their mutations.

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"math"
	"math/rand"
	"os"
	"strings"
	"testing"

	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

const wireVectorsPath = "../../Proof/google_golang_org/protobuf/proto/EntryWireVectors.lean"

var cc2Sch = map[int]fdesc{1: {k: kEnum}, 2: {k: kRepMsg, sub: "ConfChangeSingle"}, 3: {k: kBytes}}
var ccsSch = map[int]fdesc{1: {k: kEnum}, 2: {k: kU64}}

var validUF = ufOpts{innerNumMax: innerMax}
var badUF = ufOpts{nonMinOuter: true, badNums: true, badEnds: true, takenOK: true, innerNumMax: innerMax + 8}

func lh(b []byte) string { return fmt.Sprintf("(h %q)", hex.EncodeToString(b)) }

func randU64(r *rand.Rand) uint64 {
	switch r.Intn(5) {
	case 0:
		return 0
	case 1:
		return uint64(r.Intn(200))
	case 2:
		return math.MaxUint64 - uint64(r.Intn(3))
	case 3:
		return 1 << uint(r.Intn(64))
	}
	return r.Uint64()
}

func randEnum(r *rand.Rand) int32 {
	switch r.Intn(4) {
	case 0:
		return int32(r.Intn(3))
	case 1:
		return -1 - int32(r.Intn(5))
	case 2:
		return []int32{math.MaxInt32, math.MinInt32, 127, 128}[r.Intn(4)]
	}
	return int32(r.Uint32())
}

func randData(r *rand.Rand) []byte {
	switch r.Intn(6) {
	case 0:
		return nil
	case 1:
		return []byte{}
	case 2:
		b := make([]byte, 128+r.Intn(200))
		r.Read(b)
		return b
	}
	b := make([]byte, 1+r.Intn(16))
	r.Read(b)
	return b
}

func randEntry(r *rand.Rand) *pb.Entry {
	e := &pb.Entry{}
	if r.Intn(2) == 0 {
		t := pb.EntryType(randEnum(r))
		e.Type = &t
	}
	if r.Intn(2) == 0 {
		v := randU64(r)
		e.Term = &v
	}
	if r.Intn(2) == 0 {
		v := randU64(r)
		e.Index = &v
	}
	e.Data = randData(r)
	if r.Intn(2) == 0 {
		setUF(e, genUF(r, schemas["Entry"], validUF))
	}
	return e
}

func optU64(p *uint64) string {
	if p == nil {
		return "none"
	}
	return fmt.Sprintf("(some %d)", *p)
}

// mutateW: one random byte-level change of b.
func mutateW(r *rand.Rand, b []byte, pool [][]byte) []byte {
	c := append([]byte(nil), b...)
	switch r.Intn(6) {
	case 0:
		if len(c) > 0 {
			i := r.Intn(len(c))
			c[i] ^= byte(1 << uint(r.Intn(8)))
		}
	case 1:
		if len(c) > 0 {
			c = c[:r.Intn(len(c))]
		}
	case 2:
		i := r.Intn(len(c) + 1)
		c = append(c[:i], append([]byte{byte(r.Intn(256))}, c[i:]...)...)
	case 3:
		if len(c) > 0 {
			i := r.Intn(len(c))
			c = append(c[:i], c[i+1:]...)
		}
	case 4:
		o := pool[r.Intn(len(pool))]
		c = append(c, o...)
	default:
		if len(c) > 0 {
			i := r.Intn(len(c))
			c[i] = []byte{0x80, 0xff, 0x00, 0x7f, 0x01}[r.Intn(5)]
		}
	}
	return c
}

func tagB(num uint64, wt int) []byte { return protowire.AppendVarint(nil, num<<3|uint64(wt)) }

// edge cases for an Entry's decoder.
func entryEdges() [][]byte {
	cat := func(bs ...[]byte) []byte { return bytes.Join(bs, nil) }
	ten := func(last byte) []byte { // a 10-byte varint
		return append(bytes.Repeat([]byte{0xff}, 9), last)
	}
	return [][]byte{
		{},
		cat(tagB(2, 0), ten(0x01)),               // 2^64 - 1
		cat(tagB(2, 0), ten(0x02)),               // overflow
		cat(tagB(2, 0), ten(0x81), []byte{0x00}), // 11 bytes
		cat(tagB(2, 0), []byte{0x80, 0x80, 0x00}),               // non-minimal 0
		cat([]byte{0x90, 0x00}, []byte{0x05}),                   // non-minimal tag of Term
		cat(tagB(1, 0), ten(0x01)),                              // enum -1 (sign-extended)
		cat(tagB(1, 0), []byte{0x80, 0x80, 0x80, 0x80, 0x10}),   // enum 2^32: low bits 0
		cat(tagB(1, 0), []byte{0xff, 0xff, 0xff, 0xff, 0x0f}),   // enum 2^32-1
		cat(tagB(4, 2), []byte{0x00}),                           // empty Data
		cat(tagB(4, 2), []byte{0x05, 0x01}),                     // Data truncated
		cat(tagB(4, 2), ten(0x01)),                              // huge length
		cat(tagB(2, 0), []byte{0x01}, tagB(2, 0), []byte{0x02}), // last wins
		cat(tagB(4, 2), []byte{0x01, 0xaa}, tagB(4, 2), []byte{0x00}),
		cat(tagB(2, 2), []byte{0x01, 0x07}), // Term with the wrong wire type: unknown
		cat(tagB(4, 0), []byte{0x07}),       // Data with the wrong wire type: unknown
		{0x00},                              // number 0
		{0x08},                              // Type without a value
		tagB(5, 4),                          // end group at the top
		tagB(5, 6),
		tagB(5, 7),
		cat(tagB(1<<29-1, 0), []byte{0x01}),
		cat(tagB(1<<29, 0), []byte{0x01}),
		cat(tagB(5, 3), tagB(1<<31-1, 0), []byte{0x01}, tagB(5, 4)),
		cat(tagB(5, 3), tagB(1<<31, 0), []byte{0x01}, tagB(5, 4)),
		cat(tagB(5, 3), tagB(6, 4)),             // mismatched end
		cat(tagB(5, 3), tagB(5, 3), tagB(5, 4)), // unclosed
		cat(tagB(5, 3), []byte{0xac, 0x00}),     // a non-minimal end tag
		cat(tagB(6, 1), make([]byte, 8)),
		cat(tagB(6, 1), make([]byte, 7)),
		cat(tagB(6, 5), make([]byte, 4)),
		cat(tagB(6, 5), make([]byte, 3)),
		cat(tagB(1, 0), []byte{0x02}, tagB(2, 0), []byte{0x03}, tagB(3, 0), []byte{0x04}, tagB(4, 2), []byte{0x01, 0x09}, tagB(7, 2), []byte{0x00}),
	}
}

type entOut struct {
	ok        bool
	term, idx uint64
	typ       uint32
	data, uf  []byte
}

func unmarshalEntry(b []byte) entOut {
	var e pb.Entry
	if err := proto.Unmarshal(b, &e); err != nil {
		return entOut{}
	}
	return entOut{true, e.GetTerm(), e.GetIndex(), uint32(e.GetType()), e.GetData(), e.ProtoReflect().GetUnknown()}
}

func (o entOut) lean(in string) string {
	if !o.ok {
		return fmt.Sprintf("#guard entDec %s = (none, none)", in)
	}
	return fmt.Sprintf("#guard entDec %s = (some (%d, %d, %d, %s), some %s)", in, o.term, o.idx, o.typ, lh(o.data), lh(o.uf))
}

type ccOut struct {
	ok  bool
	tr  uint32
	chs [][2]uint64
	ctx []byte
}

func unmarshalCC2(b []byte) ccOut {
	var c pb.ConfChangeV2
	if err := proto.Unmarshal(b, &c); err != nil {
		return ccOut{}
	}
	o := ccOut{ok: true, tr: uint32(c.GetTransition()), ctx: c.GetContext()}
	for _, ch := range c.GetChanges() {
		o.chs = append(o.chs, [2]uint64{uint64(uint32(ch.GetType())), ch.GetNodeId()})
	}
	return o
}

func (o ccOut) lean(in string) string {
	if !o.ok {
		return fmt.Sprintf("#guard cc2DecodeRaw %s = none", in)
	}
	var cs []string
	for _, c := range o.chs {
		cs = append(cs, fmt.Sprintf("(%d, %d)", c[0], c[1]))
	}
	return fmt.Sprintf("#guard cc2DecodeRaw %s = some (%d, [%s], %s)", in, o.tr, strings.Join(cs, ", "), lh(o.ctx))
}

func randCCS(r *rand.Rand) *pb.ConfChangeSingle {
	c := &pb.ConfChangeSingle{}
	if r.Intn(3) > 0 {
		t := pb.ConfChangeType(randEnum(r))
		c.Type = &t
	}
	if r.Intn(3) > 0 {
		v := randU64(r)
		c.NodeId = &v
	}
	if r.Intn(3) == 0 {
		setUF(c, genUF(r, ccsSch, validUF))
	}
	return c
}

func randCC2(r *rand.Rand) *pb.ConfChangeV2 {
	c := &pb.ConfChangeV2{}
	if r.Intn(2) == 0 {
		t := pb.ConfChangeTransition(randEnum(r))
		c.Transition = &t
	}
	for k := r.Intn(4); k > 0; k-- {
		c.Changes = append(c.Changes, randCCS(r))
	}
	if r.Intn(2) == 0 {
		c.Context = randData(r)
	}
	if r.Intn(3) == 0 {
		setUF(c, genUF(r, cc2Sch, validUF))
	}
	return c
}

// a random sequence of ConfChangeV2 records, valid or not.
func randCC2Records(r *rand.Rand) []byte {
	var b []byte
	for k := r.Intn(6); k > 0; k-- {
		switch r.Intn(6) {
		case 0:
			b = tagPad(b, 1, 0, rpad(r))
			b = appendVarintPad(b, rval(r), rpad(r))
		case 1, 2:
			var sub []byte
			if r.Intn(4) == 0 {
				sub = genAdv(r, "Entry", 1) // garbage for a ConfChangeSingle, often invalid
			} else {
				sub, _ = proto.Marshal(randCCS(r))
				if r.Intn(4) == 0 {
					sub = append(sub, tagB(1, 0)...)
					sub = append(sub, byte(r.Intn(128)))
				}
			}
			b = protowire.AppendTag(b, 2, 2)
			b = protowire.AppendBytes(b, sub)
		case 3:
			b = protowire.AppendTag(b, 3, 2)
			b = protowire.AppendBytes(b, randData(r))
		case 4:
			b = append(b, genUF(r, cc2Sch, validUF)...)
		default:
			b = append(b, genUnknownField(r, 1+r.Intn(4), rwt(r), 0, r.Intn(2) == 0)...)
		}
	}
	return b
}

func buildWireVectors(t *testing.T) string {
	r := rand.New(rand.NewSource(37))
	var out []string
	var pool [][]byte

	out = append(out, "/-! ## `Entry`: `proto.Marshal` -/", "")
	for i := 0; i < 120; i++ {
		e := randEntry(r)
		b, err := proto.Marshal(e)
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if proto.Size(e) != len(b) {
			t.Fatalf("Size %d != len %d", proto.Size(e), len(b))
		}
		o := unmarshalEntry(b)
		if !o.ok || o.term != e.GetTerm() || o.idx != e.GetIndex() || o.typ != uint32(e.GetType()) ||
			!bytes.Equal(o.data, e.GetData()) || !bytes.Equal(o.uf, e.ProtoReflect().GetUnknown()) {
			t.Fatalf("round trip of %v: %+v", e, o)
		}
		typ := "none"
		if e.Type != nil {
			typ = fmt.Sprintf("(some %d)", uint32(*e.Type))
		}
		data := "none"
		if e.Data != nil {
			data = fmt.Sprintf("(some %s)", lh(e.Data))
		}
		out = append(out, fmt.Sprintf("#guard entryEncRaw %s %s %s %s %s = %s", typ, optU64(e.Term),
			optU64(e.Index), data, lh(e.ProtoReflect().GetUnknown()), lh(b)))
		pool = append(pool, b)
	}

	out = append(out, "", "/-! ## `Entry`: `proto.Unmarshal` -/", "")
	var ins [][]byte
	ins = append(ins, pool...)
	for i := 0; i < 60; i++ {
		ins = append(ins, encodeWithUF(r, "Entry", 0, validUF))
	}
	for i := 0; i < 60; i++ {
		ins = append(ins, encodeWithUF(r, "Entry", 0, badUF))
		ins = append(ins, genAdv(r, "Entry", 0))
	}
	base := append([][]byte(nil), ins...)
	for i := 0; i < 240; i++ {
		ins = append(ins, mutateW(r, base[r.Intn(len(base))], base))
	}
	ins = append(ins, entryEdges()...)
	for _, b := range ins {
		out = append(out, unmarshalEntry(b).lean(lh(b)))
	}
	// groups nested 10001 deep decode, 10002 do not
	for _, d := range []int{3, 10001, 10002} {
		b := deepGroup(5, d, false)
		in := fmt.Sprintf("(deep 5 %d)", d)
		// the unknown fields are the whole input: named, not spelled out
		out = append(out, strings.Replace(unmarshalEntry(b).lean(in), lh(b), in, 1))
	}

	out = append(out, "", "/-! ## `ConfChangeV2`: `proto.Unmarshal` -/", "")
	var cins [][]byte
	for i := 0; i < 60; i++ {
		c := randCC2(r)
		b, err := proto.Marshal(c)
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		o := unmarshalCC2(b)
		if !o.ok || o.tr != uint32(c.GetTransition()) || len(o.chs) != len(c.Changes) || !bytes.Equal(o.ctx, c.GetContext()) {
			t.Fatalf("round trip of %v: %+v", c, o)
		}
		cins = append(cins, b)
	}
	for i := 0; i < 80; i++ {
		cins = append(cins, randCC2Records(r))
	}
	cbase := append([][]byte(nil), cins...)
	for i := 0; i < 120; i++ {
		cins = append(cins, mutateW(r, cbase[r.Intn(len(cbase))], cbase))
	}
	cins = append(cins, []byte{}, []byte{0x12, 0x00}, []byte{0x12, 0x02, 0x08}, []byte{0x08, 0x80, 0x80, 0x80, 0x80, 0x10})
	for _, b := range cins {
		out = append(out, unmarshalCC2(b).lean(lh(b)))
	}
	return strings.Join(out, "\n")
}

const wireVectorsHeader = `/-
**The wire codecs' vectors** (protobuf trust-boundary stage S1, mit-pdos/etcd-grove#37): protobuf-go
v1.36.12's ` + "`proto.Marshal`" + ` of ` + "`raftpb.Entry`" + `s and ` + "`proto.Unmarshal`" + ` of ` + "`Entry`" + `s and
` + "`ConfChangeV2`" + `s, checked by ` + "`#guard`" + ` against the Lean codecs ` + "`entryEncRaw`" + `, ` + "`entDecodeRaw`" + ` (with the
unknown fields ` + "`decode entrySchema`" + ` leaves) and ` + "`cc2DecodeRaw`" + ` (` + "`Proof/go_etcd_io/raft/v3/PbWireRaft.lean`" + `),
which ` + "`entryEncC`" + `, ` + "`entDecode`" + ` and ` + "`ccDecodeV2`" + ` are. GENERATED by ` + "`examples/pbschema/wirevectors_test.go`" + `
(` + "`TestWireVectors`" + `, which fails if this file is not what it generates): do not edit; rerun
` + "`cd examples && WIREVECTORS_UPDATE=1 GOWORK=off go test -run '^TestWireVectors$' ./pbschema/`" + `.
-/
module

public import Proof.go_etcd_io.raft.v3.PbWireRaft
-- the #guards run the codecs at elaboration time
public meta import Proof.go_etcd_io.raft.v3.PbWireRaft

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WireVectors

open Wire

/-- The bytes of a hex string. -/
def h (s : String) : List w8 :=
  let d (c : Char) : Nat := if c.toNat ≤ '9'.toNat then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List w8
    | a :: b :: t => BitVec.ofNat 8 (16 * d a + d b) :: go t
    | _ => []
  go s.toList

/-- Groups numbered ` + "`num`" + ` nested ` + "`n`" + ` deep (minimal tags; ` + "`deepGroup`" + ` of the Go test). -/
def deep (num n : Nat) : List w8 :=
  (List.replicate n (tag num 3)).flatten ++ (List.replicate n (tag num 4)).flatten

/-- An entry's decoding: the getters, and the unknown fields. -/
def entDec (bs : List w8) : Option (w64 × w64 × w32 × List w8) × Option (List w8) :=
  (entDecodeRaw bs, (decode entrySchema bs).map (·.2))

`

func TestWireVectors(t *testing.T) {
	body := buildWireVectors(t)
	text := wireVectorsHeader + body + "\n\nend WireVectors\nend EtcdGrove\nend Perennial\n"
	if os.Getenv("WIREVECTORS_UPDATE") == "1" {
		if err := os.WriteFile(wireVectorsPath, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		return
	}
	old, err := os.ReadFile(wireVectorsPath)
	if err != nil {
		t.Fatal(err)
	}
	if string(old) != text {
		t.Fatalf("%s is not what TestWireVectors generates: rerun with WIREVECTORS_UPDATE=1", wireVectorsPath)
	}
}
