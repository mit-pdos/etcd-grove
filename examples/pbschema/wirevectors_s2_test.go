package pbschema

// The protobuf trust boundary's stage S2 (mit-pdos/etcd-grove#37): the evidence that the Lean wire
// codecs of raftpb's Message (and its Snapshot, SnapshotMetadata and ConfState) and of walpb's Record
// are protobuf-go's. Since S2, `msgEncC` (rafthttp's PerTypeMessage.lean) is `msgEncRaw` at each
// level, `msgDecode` (raft's PbMessage.lean) is `msgDecodeRaw` (Proof/go_etcd_io/raft/v3/PbWireRaft.lean),
// and `recDecode` (wal/walpb/PbRecord.lean) is `recDecodeRaw` (storage/WalPbWire.lean), next to the
// encoder `recEnc` that was already a Lean function; so the trusted specs of proto.Marshal and
// proto.Unmarshal at these types claim that protobuf-go v1.36.12 (examples/go.mod's pin) computes
// them.
//
// TestMessageWireVectors and TestRecordWireVectors build the vectors from protobuf-go (fixed seeds)
// and compare them with the Lean modules MessageWireVectors.lean and RecordWireVectors.lean, whose
// #guards check the Lean functions against every vector when they are built; WIREVECTORS_UPDATE=1
// rewrites the modules instead.
//
//   - Message, encode: proto.Marshal of random Messages (every optional field present or not,
//     zero values, enums out of range, nil/empty/long bytes, entries, a snapshot with or without
//     metadata and conf state, responses with their own entries and snapshots, unknown fields at
//     every level), as the Lean composition of msgEncRaw, entryEncRaw, snapEncRaw, metaEncRaw and
//     csEncRaw (the responses as msgEncRaw too); checked here against proto.Size.
//   - Message, decode: proto.Unmarshal's outcome (every getter, a conf state's lists, the number of
//     responses, or an error) on those encodings, on valid encodings with unknown fields interleaved
//     at every level, adversarial ones (packed and unpacked repeated fields, wrong wire types,
//     non-minimal tags, Responses), byte mutations of all of them, and edge cases: a snapshot, its
//     metadata and its conf state split over several records (merged), packed lists that do not
//     parse, bools other than 0 and 1, last-one-wins, an empty entry, Responses nested 300 deep and
//     with an invalid innermost message. (The recursion limit, 10000 nested messages, is checked in
//     Go only, TestMessageDepthLimit: the Lean decoder's cost is quadratic in the nesting.)
//   - Record: proto.Marshal of random Records as recEnc, and proto.Unmarshal's outcome as
//     recDecodeRaw on encodings, adversarial ones, mutations and edge cases (int64 and uint32
//     truncation of 10-byte varints).

import (
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"strings"
	"testing"

	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"

	epb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	pb "go.etcd.io/raft/v3/raftpb"
)

const msgVectorsPath = "../../Proof/google_golang_org/protobuf/proto/MessageWireVectors.lean"
const recVectorsPath = "../../Proof/google_golang_org/protobuf/proto/RecordWireVectors.lean"

func lOptU64(p *uint64) string {
	if p == nil {
		return "none"
	}
	return fmt.Sprintf("(some %d)", *p)
}

func lOptEnum(p *int32) string {
	if p == nil {
		return "none"
	}
	return fmt.Sprintf("(some %d)", uint32(*p))
}

func lOptBool(p *bool) string {
	if p == nil {
		return "none"
	}
	return fmt.Sprintf("(some %t)", *p)
}

func lOptData(p *[]byte) string {
	if p == nil {
		return "none"
	}
	return fmt.Sprintf("(some %s)", lh(*p))
}

func lU64s(xs []uint64) string {
	var s []string
	for _, x := range xs {
		s = append(s, fmt.Sprint(x))
	}
	return "[" + strings.Join(s, ", ") + "]"
}

// the Lean expression of the encoding of a content: the raw encoders composed.
func leanEntEnc(e entC) string {
	return fmt.Sprintf("(entryEncRaw %s %s %s %s %s)", lOptEnum(e.typ), lOptU64(e.term), lOptU64(e.index), lOptData(e.data), lh(e.uf))
}

func leanCSEnc(c *csC) string {
	return fmt.Sprintf("(csEncRaw %s %s %s %s %s %s)", lU64s(c.voters), lU64s(c.learners), lU64s(c.vout), lU64s(c.lnext), lOptBool(c.autoLeave), lh(c.uf))
}

func leanMetaEnc(m *metaC) string {
	cs := "none"
	if m.cs != nil {
		cs = "(some " + leanCSEnc(m.cs) + ")"
	}
	return fmt.Sprintf("(metaEncRaw %s %s %s %s)", cs, lOptU64(m.index), lOptU64(m.term), lh(m.uf))
}

func leanSnapEnc(s *snapC) string {
	md := "none"
	if s.meta != nil {
		md = "(some " + leanMetaEnc(s.meta) + ")"
	}
	return fmt.Sprintf("(snapEncRaw %s %s %s)", lOptData(s.data), md, lh(s.uf))
}

func leanMsgEnc(c msgC) string {
	var ents, resps []string
	for _, e := range c.entries {
		ents = append(ents, leanEntEnc(e))
	}
	for _, r := range c.resps {
		resps = append(resps, leanMsgEnc(r))
	}
	snap := "none"
	if c.snap != nil {
		snap = "(some " + leanSnapEnc(c.snap) + ")"
	}
	return fmt.Sprintf("(msgEncRaw %s %s %s %s %s %s [%s] %s %s %s %s %s %s [%s] %s)", lOptEnum(c.typ), lOptU64(c.to),
		lOptU64(c.from), lOptU64(c.term), lOptU64(c.logTerm), lOptU64(c.index), strings.Join(ents, ", "),
		lOptU64(c.commit), snap, lOptBool(c.reject), lOptU64(c.rejectHint), lOptData(c.context), lOptU64(c.vote),
		strings.Join(resps, ", "), lh(c.uf))
}

// the Lean MsgDec of what the getters return after a successful Unmarshal.
func leanMsgDec(m *pb.Message) string {
	var ents []string
	for _, e := range m.GetEntries() {
		ents = append(ents, fmt.Sprintf("(%d, %d, %d, %s)", e.GetTerm(), e.GetIndex(), uint32(e.GetType()), lh(e.GetData())))
	}
	snap := "none"
	if s := m.GetSnapshot(); s != nil {
		md := s.GetMetadata()
		cs := md.GetConfState()
		snap = fmt.Sprintf("(some ⟨%s, ⟨⟨%s, %s, %s, %s, %t⟩, %d, %d⟩⟩)", lh(s.GetData()), lU64s(cs.GetVoters()),
			lU64s(cs.GetLearners()), lU64s(cs.GetVotersOutgoing()), lU64s(cs.GetLearnersNext()), cs.GetAutoLeave(),
			md.GetIndex(), md.GetTerm())
	}
	return fmt.Sprintf("some ⟨%d, %d, %d, %d, %d, %d, [%s], %d, %s, %t, %d, %s, %d, %d⟩", uint32(m.GetType()),
		m.GetTo(), m.GetFrom(), m.GetTerm(), m.GetLogTerm(), m.GetIndex(), strings.Join(ents, ", "), m.GetCommit(),
		snap, m.GetReject(), m.GetRejectHint(), lh(m.GetContext()), m.GetVote(), len(m.GetResponses()))
}

func msgDecGuard(b []byte, in string) string {
	var m pb.Message
	if err := proto.Unmarshal(b, &m); err != nil {
		return fmt.Sprintf("#guard msgDecodeRaw %s = none", in)
	}
	return fmt.Sprintf("#guard msgDecodeRaw %s = %s", in, leanMsgDec(&m))
}

func randMsgCResp(t *testing.T, r *rand.Rand) msgC {
	c := randMsgC(t, r)
	if r.Intn(4) == 0 {
		for k := 1 + r.Intn(2); k > 0; k-- {
			c.resps = append(c.resps, randMsgC(t, r))
		}
	}
	return c
}

func cat(bs ...[]byte) []byte { return bytes.Join(bs, nil) }

func lenRec(num uint64, body []byte) []byte {
	return protowire.AppendBytes(tagB(num, 2), body)
}

func varRec(num uint64, v uint64) []byte {
	return protowire.AppendVarint(tagB(num, 0), v)
}

// nested Responses: d levels, the innermost message inner.
func nestedResp(d int, inner []byte) []byte {
	m := inner
	for i := 0; i < d; i++ {
		m = lenRec(14, m)
	}
	return m
}

func messageEdges() [][]byte {
	cs1 := cat(varRec(1, 1), varRec(5, 1))
	cs2 := cat(lenRec(1, []byte{0x02, 0x03}), varRec(2, 7), lenRec(3, nil))
	md := func(cs []byte, more ...[]byte) []byte { return cat(append([][]byte{lenRec(1, cs)}, more...)...) }
	snap := func(m []byte, more ...[]byte) []byte { return cat(append([][]byte{lenRec(2, m)}, more...)...) }
	return [][]byte{
		{},
		lenRec(9, nil),                     // an empty snapshot: present
		lenRec(9, lenRec(2, nil)),          // empty metadata
		lenRec(9, lenRec(2, lenRec(1, nil))), // empty conf state
		// a snapshot over two records: merged (metadata, conf state and data)
		cat(lenRec(9, snap(md(cs1), lenRec(1, []byte{0xaa}))), lenRec(9, snap(md(cs2, varRec(2, 9)), lenRec(1, []byte{0xbb})))),
		// metadata over two records within one snapshot
		lenRec(9, cat(lenRec(2, md(cs1, varRec(3, 4))), lenRec(2, md(cs2)))),
		// packed lists that do not parse
		lenRec(9, snap(md(lenRec(1, []byte{0x80})))),
		lenRec(9, snap(md(lenRec(4, []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02})))),
		lenRec(9, snap(md(lenRec(2, []byte{0x01, 0x80, 0x80, 0x00})))), // non-minimal packed value
		// auto_leave and reject other than 0 and 1, last one wins
		cat(varRec(10, 2), varRec(10, 0), varRec(10, 5)),
		lenRec(9, snap(md(cat(varRec(5, 3), varRec(5, 0))))),
		// an empty entry, an entry with an unknown field, an invalid entry
		lenRec(7, nil),
		cat(lenRec(7, cat(varRec(2, 5), varRec(99, 1))), lenRec(7, varRec(3, 1))),
		cat(lenRec(7, varRec(2, 5)), lenRec(7, []byte{0x10})),
		// Responses: valid, with entries, invalid inside
		lenRec(14, nil),
		cat(lenRec(14, cat(varRec(2, 3), lenRec(7, varRec(2, 1)))), lenRec(14, lenRec(14, nil))),
		lenRec(14, []byte{0x08}),
		nestedResp(300, cat(varRec(2, 7), lenRec(9, snap(md(cs1))))),
		nestedResp(300, []byte{0x08}),
		// the context: last one wins, empty
		cat(lenRec(12, []byte{1, 2}), lenRec(12, nil)),
		// wrong wire types for message fields: unknown
		cat(varRec(9, 1), varRec(7, 2), varRec(14, 3), varRec(12, 4)),
		// a type out of range, a 10-byte enum
		cat(varRec(1, 1<<40|5)),
		cat(tagB(1, 0), bytes.Repeat([]byte{0xff}, 9), []byte{0x01}),
	}
}

func buildMessageVectors(t *testing.T) string {
	r := rand.New(rand.NewSource(3702))
	var out []string
	var pool [][]byte

	out = append(out, "/-! ## `Message`: `proto.Marshal` -/", "")
	for i := 0; i < 150; i++ {
		c := randMsgCResp(t, r)
		m := toPbMsg(c)
		b, err := proto.Marshal(m)
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if proto.Size(m) != len(b) {
			t.Fatalf("Size %d != len %d", proto.Size(m), len(b))
		}
		out = append(out, fmt.Sprintf("#guard %s = %s", leanMsgEnc(c), lh(b)))
		pool = append(pool, b)
	}

	out = append(out, "", "/-! ## `Message`: `proto.Unmarshal` -/", "")
	var ins [][]byte
	ins = append(ins, pool...)
	for i := 0; i < 80; i++ {
		ins = append(ins, encodeWithUF(r, "Message", 0, validUF))
	}
	for i := 0; i < 80; i++ {
		ins = append(ins, encodeWithUF(r, "Message", 0, badUF))
		ins = append(ins, genAdv(r, "Message", 0))
	}
	for i := 0; i < 10; i++ {
		ins = append(ins, packedConfStateMsg(1+r.Intn(40), 1+r.Intn(4), r.Intn(3)))
	}
	base := append([][]byte(nil), ins...)
	for i := 0; i < 400; i++ {
		ins = append(ins, mutateW(r, base[r.Intn(len(base))], base))
	}
	ins = append(ins, messageEdges()...)
	for _, b := range ins {
		out = append(out, msgDecGuard(b, lh(b)))
	}

	// D2 (kaashoek, #37): a message decoded from records with unknown fields interleaved at every
	// level, re-encoded: protobuf-go writes the known fields in field-number order and the unknown
	// fields, kept in arrival order, after them; the Lean encoder of the decoded content agrees.
	out = append(out, "", "/-! ## `Message`: `proto.Marshal` of decoded messages (unknown fields interleaved) -/", "")
	nre := 0
	for i := 0; nre < 80 && i < 2000; i++ {
		b := encodeWithUF(r, "Message", 0, validUF)
		if r.Intn(3) == 0 {
			b = append(b, encodeWithUF(r, "Message", 0, validUF)...)
		}
		var m pb.Message
		if proto.Unmarshal(b, &m) != nil || len(m.ProtoReflect().GetUnknown()) == 0 {
			continue
		}
		re, err := proto.Marshal(&m)
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if bytes.Equal(re, b) {
			continue // already canonical: not an interleaving
		}
		out = append(out, fmt.Sprintf("#guard %s = %s", leanMsgEnc(contentOfMsg(&m)), lh(re)))
		nre++
	}
	if nre < 80 {
		t.Fatalf("only %d re-encoded interleavings", nre)
	}
	return strings.Join(out, "\n")
}

// TestMessageDepthLimit: proto.Unmarshal decodes Messages nested 10000 deep (the top one included)
// and fails at 10001, as msgDecodeRaw's depth (msgDecodeD 10000) says; an entry or a snapshot is a
// level too.
func TestMessageDepthLimit(t *testing.T) {
	try := func(b []byte) bool {
		var m pb.Message
		return proto.Unmarshal(b, &m) == nil
	}
	if !try(nestedResp(9999, nil)) || try(nestedResp(10000, nil)) {
		t.Fatal("Responses: 10000 levels decode, 10001 do not")
	}
	if !try(nestedResp(9998, lenRec(7, nil))) || try(nestedResp(9999, lenRec(7, nil))) {
		t.Fatal("an entry at level 10000 decodes, at 10001 not")
	}
	if !try(nestedResp(9996, lenRec(9, lenRec(2, lenRec(1, nil))))) || try(nestedResp(9997, lenRec(9, lenRec(2, lenRec(1, nil))))) {
		t.Fatal("a conf state at level 10000 decodes, at 10001 not")
	}
	// an absent sub-message costs no level
	if !try(nestedResp(9999, varRec(2, 1))) {
		t.Fatal("scalars at level 10000")
	}
}

var recSch = map[int]fdesc{1: {k: kU64}, 2: {k: kU64}, 3: {k: kBytes}}

func randRecord(r *rand.Rand) *walpb.Record {
	rec := &walpb.Record{}
	if r.Intn(4) != 0 {
		v := int64(randU64(r))
		rec.Type = &v
	}
	if r.Intn(4) != 0 {
		v := uint32(randU64(r))
		rec.Crc = &v
	}
	rec.Data = randData(r)
	if r.Intn(3) == 0 {
		setUF(rec, genUF(r, recSch, validUF))
	}
	return rec
}

func recEncGuard(rec *walpb.Record, b []byte) string {
	typ, crc := "none", "none"
	if rec.Type != nil {
		typ = fmt.Sprintf("(some %d)", uint64(*rec.Type))
	}
	if rec.Crc != nil {
		crc = fmt.Sprintf("(some %d)", *rec.Crc)
	}
	data := "none"
	if rec.Data != nil {
		data = fmt.Sprintf("(some %s)", lh(rec.Data))
	}
	return fmt.Sprintf("#guard recEnc ⟨%s, %s, %s, %s⟩ = %s", typ, crc, data, lh(rec.ProtoReflect().GetUnknown()), lh(b))
}

func recDecGuard(b []byte) string {
	var rec walpb.Record
	if err := proto.Unmarshal(b, &rec); err != nil {
		return fmt.Sprintf("#guard recDecodeRaw %s = none", lh(b))
	}
	return fmt.Sprintf("#guard recDecodeRaw %s = some ⟨%d, %d, %s⟩", lh(b), uint64(rec.GetType()), rec.GetCrc(), lh(rec.GetData()))
}

// a random sequence of Record fields, valid or not.
func randRecRecords(r *rand.Rand) []byte {
	var b []byte
	for k := r.Intn(6); k > 0; k-- {
		switch r.Intn(5) {
		case 0, 1:
			b = tagPad(b, 1+r.Intn(2), 0, rpad(r))
			b = appendVarintPad(b, rval(r), rpad(r))
		case 2:
			b = append(b, lenRec(3, randData(r))...)
		case 3:
			b = append(b, genUF(r, recSch, validUF)...)
		default:
			b = append(b, genUnknownField(r, 1+r.Intn(4), rwt(r), 0, r.Intn(2) == 0)...)
		}
	}
	return b
}

func buildRecordVectors(t *testing.T) string {
	r := rand.New(rand.NewSource(3703))
	var out []string
	var pool [][]byte
	out = append(out, "/-! ## `walpb.Record`: `proto.Marshal` -/", "")
	for i := 0; i < 100; i++ {
		rec := randRecord(r)
		b, err := proto.Marshal(rec)
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if proto.Size(rec) != len(b) {
			t.Fatalf("Size %d != len %d", proto.Size(rec), len(b))
		}
		out = append(out, recEncGuard(rec, b))
		pool = append(pool, b)
	}
	out = append(out, "", "/-! ## `walpb.Record`: `proto.Unmarshal` -/", "")
	var ins [][]byte
	ins = append(ins, pool...)
	for i := 0; i < 100; i++ {
		ins = append(ins, randRecRecords(r))
	}
	base := append([][]byte(nil), ins...)
	for i := 0; i < 200; i++ {
		ins = append(ins, mutateW(r, base[r.Intn(len(base))], base))
	}
	ten := append(bytes.Repeat([]byte{0xff}, 9), 0x01)
	ins = append(ins,
		[]byte{},
		cat(tagB(1, 0), ten),                     // Type -1
		cat(tagB(2, 0), ten),                     // Crc: the low 32 bits
		cat(tagB(2, 0), []byte{0x80, 0x80, 0x80, 0x80, 0x10}), // Crc 2^32: 0
		cat(varRec(1, 3), varRec(1, 4)),          // last one wins
		cat(lenRec(3, []byte{1}), lenRec(3, nil)), // Data last one wins
		cat(varRec(3, 1)),                        // Data with the wrong wire type: unknown
		lenRec(1, []byte{1}),                     // Type with the wrong wire type: unknown
		cat(tagB(3, 2), []byte{0x05, 0x01}),      // truncated
	)
	for _, b := range ins {
		out = append(out, recDecGuard(b))
	}
	// D2: decoded records with unknown fields interleaved, re-encoded
	out = append(out, "", "/-! ## `walpb.Record`: `proto.Marshal` of decoded records (unknown fields interleaved) -/", "")
	nre := 0
	for _, b := range ins {
		var rec walpb.Record
		if proto.Unmarshal(b, &rec) != nil || len(rec.ProtoReflect().GetUnknown()) == 0 {
			continue
		}
		re, err := proto.Marshal(&rec)
		if err != nil || bytes.Equal(re, b) {
			continue
		}
		out = append(out, recEncGuard(&rec, re))
		nre++
	}
	if nre < 20 {
		t.Fatalf("only %d re-encoded records", nre)
	}
	return strings.Join(out, "\n")
}

const vectorsHelpers = `/-- The bytes of a hex string. -/
def h (s : String) : List w8 :=
  let d (c : Char) : Nat := if c.toNat ≤ '9'.toNat then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List w8
    | a :: b :: t => BitVec.ofNat 8 (16 * d a + d b) :: go t
    | _ => []
  go s.toList

`

func vectorsHeader(what, codecs, which, test, mod, imp, ns string) string {
	return `/-
**The wire codecs' vectors: ` + what + `** (protobuf trust-boundary stage S2, mit-pdos/etcd-grove#37):
protobuf-go v1.36.12's ` + "`proto.Marshal`" + ` and ` + "`proto.Unmarshal`" + `, checked by ` + "`#guard`" + ` against the Lean codecs
` + codecs + `, which ` + which + ` are. GENERATED by ` + "`examples/pbschema/wirevectors_s2_test.go`" + `
(` + "`" + test + "`" + `, which fails if this file is not what it generates): do not edit; rerun
` + "`cd examples && WIREVECTORS_UPDATE=1 GOWORK=off go test -run '^" + test + "$' ./pbschema/`" + `.
-/
module

public import ` + imp + `
-- the #guards run the codecs at elaboration time
public meta import ` + imp + `

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace ` + ns + `

open Wire

` + vectorsHelpers
}

func checkOrWrite(t *testing.T, path, text string) {
	if os.Getenv("WIREVECTORS_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		return
	}
	old, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(old) != text {
		t.Fatalf("%s is not what the test generates: rerun with WIREVECTORS_UPDATE=1", path)
	}
}

func TestMessageWireVectors(t *testing.T) {
	hdr := vectorsHeader("`raftpb.Message`", "`msgEncRaw`, `csEncRaw`, `metaEncRaw`, `snapEncRaw`, `entryEncRaw` and `msgDecodeRaw`\n(`Proof/go_etcd_io/raft/v3/PbWireRaft.lean`)",
		"`msgEncC` (rafthttp's `PerTypeMessage.lean`) and `msgDecode` (raft's `PbMessage.lean`)",
		"TestMessageWireVectors", "MessageWireVectors", "Proof.go_etcd_io.raft.v3.PbWireRaft", "MsgWireVectors")
	text := hdr + buildMessageVectors(t) + "\n\nend MsgWireVectors\nend EtcdGrove\nend Perennial\n"
	checkOrWrite(t, msgVectorsPath, text)
}

func TestRecordWireVectors(t *testing.T) {
	hdr := vectorsHeader("`walpb.Record`", "`WalEnc.recEnc` and `WalEnc.recDecodeRaw`\n(`Proof/go_etcd_io/etcd/server/v3/storage/WalPbWire.lean`)",
		"`recEnc` and `recDecode` (the WAL's `walpb/PbRecord.lean`)",
		"TestRecordWireVectors", "RecordWireVectors", "Proof.go_etcd_io.etcd.server.v3.storage.WalPbWire", "RecWireVectors")
	text := strings.Replace(hdr, "open Wire\n", "open Wire WalEnc\n", 1) + buildRecordVectors(t) + "\n\nend RecWireVectors\nend EtcdGrove\nend Perennial\n"
	checkOrWrite(t, recVectorsPath, text)
}

// ---------------- InternalRaftRequest's AuthUserGrantRole ----------------

const irrVectorsPath = "../../Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/IrrWireVectors.lean"

func randStr(r *rand.Rand) string {
	switch r.Intn(6) {
	case 0:
		return ""
	case 1:
		return "root"
	case 2:
		return "rôle-ünïcode-日本-\U0001F600"
	case 3:
		return strings.Repeat("x", 100+r.Intn(100))
	}
	b := make([]byte, 1+r.Intn(12))
	for i := range b {
		b[i] = byte('a' + r.Intn(26))
	}
	return string(b)
}

func randIRR(t *testing.T, r *rand.Rand) *epb.InternalRaftRequest {
	q := &epb.InternalRaftRequest{ID: randU64(r)}
	if r.Intn(2) == 0 {
		q.Header = &epb.RequestHeader{ID: randU64(r), Username: randStr(r), AuthRevision: randU64(r)}
	}
	if r.Intn(2) == 0 {
		q.AuthUserGrantRole = &epb.AuthUserGrantRoleRequest{User: randStr(r), Role: randStr(r)}
		if r.Intn(4) == 0 {
			setUF(q.AuthUserGrantRole, genUF(r, ugrSch, validUF))
		}
	}
	switch r.Intn(5) {
	case 0:
		q.Put = &epb.PutRequest{Key: []byte(randStr(r)), Value: randData(r), Lease: int64(r.Intn(100))}
	case 1:
		q.Range = &epb.RangeRequest{Key: []byte(randStr(r)), RangeEnd: []byte{0}, Limit: int64(r.Intn(5))}
	case 2:
		q.AuthRoleAdd = &epb.AuthRoleAddRequest{Name: randStr(r)}
	case 3:
		q.AuthUserRevokeRole = &epb.AuthUserRevokeRoleRequest{Name: randStr(r), Role: randStr(r)}
	}
	if r.Intn(4) == 0 {
		setUF(q, genUF(r, irrTopSch, validUF))
	}
	return q
}

var ugrSch = map[int]fdesc{1: {k: kBytes}, 2: {k: kBytes}}

// the IRR's declared fields, all taken as length-delimited or varints by the generator's unknown
// fields (genUF avoids these numbers' declared wire types: here, only 1104's matters to the reader)
var irrTopSch = map[int]fdesc{1: {k: kU64}, 100: {k: kBytes}, 102: {k: kBytes}, 103: {k: kBytes},
	1104: {k: kMsg, sub: "AuthUserGrantRoleRequest"}}

// a UGR body, valid or not: string records (valid UTF-8 or not), unknown fields, wrong wire types.
func randUGRBody(r *rand.Rand) []byte {
	var b []byte
	for k := r.Intn(5); k > 0; k-- {
		switch r.Intn(7) {
		case 0, 1:
			b = append(b, lenRec(uint64(1+r.Intn(2)), []byte(randStr(r)))...)
		case 2:
			bad := [][]byte{{0xff}, {0xc0, 0x80}, {0xed, 0xa0, 0x80}, {0xe2, 0x82}, {0xf4, 0x90, 0x80, 0x80}, {'a', 0x80}}
			b = append(b, lenRec(uint64(1+r.Intn(2)), bad[r.Intn(len(bad))])...)
		case 3:
			b = append(b, genUF(r, ugrSch, validUF)...)
		case 4:
			b = append(b, varRec(uint64(1+r.Intn(2)), rval(r))...) // a string with a varint: unknown
		default:
			b = append(b, genUnknownField(r, 1+r.Intn(4), rwt(r), 0, r.Intn(2) == 0)...)
		}
	}
	return b
}

func randIRRRecords(t *testing.T, r *rand.Rand) []byte {
	var b []byte
	for k := r.Intn(5); k > 0; k-- {
		switch r.Intn(6) {
		case 0, 1:
			b = append(b, lenRec(1104, randUGRBody(r))...)
		case 2:
			q, err := proto.Marshal(randIRR(t, r))
			if err != nil {
				t.Fatal(err)
			}
			b = append(b, q...)
		case 3:
			b = append(b, varRec(1104, rval(r))...) // wrong wire type: unknown
		case 4:
			b = append(b, genUF(r, irrTopSch, validUF)...)
		default:
			b = append(b, genUnknownField(r, []int{1, 3, 4, 100, 102, 1104, 1105}[r.Intn(7)], rwt(r), 0, r.Intn(2) == 0)...)
		}
	}
	return b
}

func buildIrrVectors(t *testing.T) (string, int) {
	r := rand.New(rand.NewSource(3704))
	var ins [][]byte
	for i := 0; i < 150; i++ {
		b, err := proto.Marshal(randIRR(t, r))
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		ins = append(ins, b)
	}
	for i := 0; i < 300; i++ {
		ins = append(ins, randIRRRecords(t, r))
	}
	base := append([][]byte(nil), ins...)
	for i := 0; i < 300; i++ {
		ins = append(ins, mutateW(r, base[r.Intn(len(base))], base))
	}
	ins = append(ins,
		[]byte{},
		lenRec(1104, nil),
		cat(lenRec(1104, lenRec(1, []byte("a"))), lenRec(1104, lenRec(2, []byte("b")))), // merged
		cat(lenRec(1104, cat(lenRec(2, []byte("x")), lenRec(2, []byte("y"))))),           // last one wins
		lenRec(1104, lenRec(2, []byte{0xff})),                                             // invalid: Go fails
		lenRec(1104, cat(lenRec(2, []byte{0xff}), lenRec(2, []byte("ok")))),              // an earlier invalid record: Go fails
	)
	var out []string
	nfail := 0
	for _, b := range ins {
		var q epb.InternalRaftRequest
		if err := proto.Unmarshal(b, &q); err != nil {
			nfail++
			continue
		}
		want := "some none"
		if u := q.AuthUserGrantRole; u != nil {
			want = fmt.Sprintf("some (some (%s, %s))", lh([]byte(u.GetUser())), lh([]byte(u.GetRole())))
		}
		out = append(out, fmt.Sprintf("#guard irrUgrDecodeRaw %s = %s", lh(b), want))
	}
	return strings.Join(out, "\n"), nfail
}

// TestIrrWireVectors: wherever protobuf-go's Unmarshal into an InternalRaftRequest succeeds, the
// Lean reader irrUgrDecodeRaw reads its AuthUserGrantRole (what irrDecode's definition claims; where
// protobuf-go fails the reader claims nothing, the opaque irrDecodeRest failing).
func TestIrrWireVectors(t *testing.T) {
	body, nfail := buildIrrVectors(t)
	if nfail < 50 {
		t.Fatalf("only %d inputs that protobuf-go rejects: the generator is too tame", nfail)
	}
	hdr := vectorsHeader("`InternalRaftRequest.AuthUserGrantRole`", "`IrrWire.irrUgrDecodeRaw`\n(`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/IrrWire.lean`), on every input protobuf-go decodes",
		"`apply.irrDecode`'s `authUserGrantRole` (`apply/InvRequest.lean`)",
		"TestIrrWireVectors", "IrrWireVectors", "Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.IrrWire", "IrrWireVectors")
	text := strings.Replace(hdr, "open Wire\n", "open Wire IrrWire\n", 1) + body + "\n\nend IrrWireVectors\nend EtcdGrove\nend Perennial\n"
	checkOrWrite(t, irrVectorsPath, text)
}
