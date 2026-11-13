package walpb

// Checks the Lean model of walpb.Snapshot's wire format (and of the raftpb.ConfState inside it),
// Proof/go_etcd_io/etcd/server/v3/storage/WalPbSnapWire.lean, against protobuf-go (the version
// examples/go.mod selects) and the walpb/raftpb packages at the forks' pins. csEnc and snapEnc below
// transcribe the Lean definitions one for one. For random wire contents (Index, Term nil or set, zero
// included; ConfState nil or a message, its four lists empty or not, AutoLeave nil, false or true;
// unknown fields at both levels, routed to the unknown fields at the level's schema) the tests
// compare proto.Marshal with snapEnc, proto.Size with snapEnc's length, and proto.Unmarshal(snapEnc c)
// with c itself (presence, the lists, the unknown fields verbatim at both levels); and the
// descriptors with walSnapSchema and walCsSchema.

import (
	"bytes"
	"math/rand"
	"slices"
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// csC is the Lean WalCsC.
type csC struct {
	voters, learners, votersOutgoing, learnersNext []uint64
	autoLeave                                      *bool
	uf                                             []byte
}

// snapC is the Lean WalSnapC.
type snapC struct {
	index, term *uint64
	cs          *csC
	uf          []byte
}

func optVarint(b []byte, num int, v *uint64) []byte {
	if v == nil {
		return b
	}
	b = append(b, varintEnc(uint64(num*8))...)
	return append(b, varintEnc(*v)...)
}

// repVarintField is the Lean repVarintField.
func repVarintField(b []byte, num int, vs []uint64) []byte {
	for _, v := range vs {
		b = append(b, varintEnc(uint64(num*8))...)
		b = append(b, varintEnc(v)...)
	}
	return b
}

// csEnc is the Lean csEnc.
func csEnc(c csC) []byte {
	var b []byte
	b = repVarintField(b, 1, c.voters)
	b = repVarintField(b, 2, c.learners)
	b = repVarintField(b, 3, c.votersOutgoing)
	b = repVarintField(b, 4, c.learnersNext)
	if c.autoLeave != nil {
		v := uint64(0)
		if *c.autoLeave {
			v = 1
		}
		b = optVarint(b, 5, &v)
	}
	return append(b, c.uf...)
}

// snapEnc is the Lean snapEnc.
func snapEnc(s snapC) []byte {
	var b []byte
	b = optVarint(b, 1, s.index)
	b = optVarint(b, 2, s.term)
	if s.cs != nil {
		d := csEnc(*s.cs)
		b = append(b, varintEnc(3*8+2)...)
		b = append(b, varintEnc(uint64(len(d)))...)
		b = append(b, d...)
	}
	return append(b, s.uf...)
}

// walSnapSchema and walCsSchema are the Lean schemas.
var walSnapSchema = map[protowire.Number][]protowire.Type{
	1: {protowire.VarintType},
	2: {protowire.VarintType},
	3: {protowire.BytesType},
}

var walCsSchema = map[protowire.Number][]protowire.Type{
	1: {protowire.VarintType, protowire.BytesType},
	2: {protowire.VarintType, protowire.BytesType},
	3: {protowire.VarintType, protowire.BytesType},
	4: {protowire.VarintType, protowire.BytesType},
	5: {protowire.VarintType},
}

// genUFAt: whole fields routed to the unknown fields at the schema s, minimal tags.
func genUFAt(r *rand.Rand, s map[protowire.Number][]protowire.Type) []byte {
	var b []byte
	for k := r.Intn(3); k > 0; k-- {
		var num protowire.Number
		var wt protowire.Type
		for {
			num = protowire.Number(1 + r.Intn(40))
			wt = []protowire.Type{protowire.VarintType, protowire.Fixed64Type, protowire.BytesType,
				protowire.Fixed32Type}[r.Intn(4)]
			if !slices.Contains(s[num], wt) {
				break
			}
		}
		b = protowire.AppendTag(b, num, wt)
		switch wt {
		case protowire.VarintType:
			b = protowire.AppendVarint(b, rval(r))
		case protowire.Fixed64Type:
			b = protowire.AppendFixed64(b, r.Uint64())
		case protowire.Fixed32Type:
			b = protowire.AppendFixed32(b, r.Uint32())
		case protowire.BytesType:
			d := make([]byte, r.Intn(20))
			r.Read(d)
			b = protowire.AppendBytes(b, d)
		}
	}
	return b
}

func genList(r *rand.Rand) []uint64 {
	var vs []uint64
	switch r.Intn(4) {
	case 0: // nil
	case 1:
		vs = []uint64{}
	default:
		for k := 1 + r.Intn(7); k > 0; k-- {
			vs = append(vs, rval(r))
		}
	}
	return vs
}

func genSnap(r *rand.Rand) snapC {
	var s snapC
	if r.Intn(5) != 0 {
		v := rval(r)
		s.index = &v
	}
	if r.Intn(5) != 0 {
		v := rval(r)
		s.term = &v
	}
	if r.Intn(4) != 0 {
		c := csC{voters: genList(r), learners: genList(r), votersOutgoing: genList(r),
			learnersNext: genList(r)}
		if k := r.Intn(3); k > 0 {
			v := k == 2
			c.autoLeave = &v
		}
		if r.Intn(3) == 0 {
			c.uf = genUFAt(r, walCsSchema)
		}
		s.cs = &c
	}
	if r.Intn(3) == 0 {
		s.uf = genUFAt(r, walSnapSchema)
	}
	return s
}

func snapToGo(s snapC) *walpb.Snapshot {
	m := &walpb.Snapshot{Index: s.index, Term: s.term}
	if s.cs != nil {
		c := &raftpb.ConfState{Voters: s.cs.voters, Learners: s.cs.learners,
			VotersOutgoing: s.cs.votersOutgoing, LearnersNext: s.cs.learnersNext, AutoLeave: s.cs.autoLeave}
		if s.cs.uf != nil {
			c.ProtoReflect().SetUnknown(protoreflect.RawFields(s.cs.uf))
		}
		m.ConfState = c
	}
	if s.uf != nil {
		m.ProtoReflect().SetUnknown(protoreflect.RawFields(s.uf))
	}
	return m
}

func sameOpt(a, b *uint64) bool { return (a == nil) == (b == nil) && (a == nil || *a == *b) }

func sameSnap(t *testing.T, m *walpb.Snapshot, s snapC, enc []byte) {
	t.Helper()
	if !sameOpt(m.Index, s.index) || !sameOpt(m.Term, s.term) {
		t.Fatalf("Index/Term differ, encoding %x", enc)
	}
	if !bytes.Equal(m.ProtoReflect().GetUnknown(), s.uf) {
		t.Fatalf("unknown fields differ, encoding %x", enc)
	}
	if (m.ConfState == nil) != (s.cs == nil) {
		t.Fatalf("ConfState presence differs, encoding %x", enc)
	}
	if s.cs == nil {
		return
	}
	c := m.ConfState
	if !slices.Equal(c.Voters, s.cs.voters) || !slices.Equal(c.Learners, s.cs.learners) ||
		!slices.Equal(c.VotersOutgoing, s.cs.votersOutgoing) || !slices.Equal(c.LearnersNext, s.cs.learnersNext) {
		t.Fatalf("ConfState lists differ, encoding %x", enc)
	}
	if (c.AutoLeave == nil) != (s.cs.autoLeave == nil) || (c.AutoLeave != nil && *c.AutoLeave != *s.cs.autoLeave) {
		t.Fatalf("AutoLeave differs, encoding %x", enc)
	}
	if !bytes.Equal(c.ProtoReflect().GetUnknown(), s.cs.uf) {
		t.Fatalf("ConfState unknown fields differ, encoding %x", enc)
	}
}

func TestSnapshotEncoder(t *testing.T) {
	r := rand.New(rand.NewSource(2))
	for i := 0; i < 200000; i++ {
		s := genSnap(r)
		want := snapEnc(s)
		m := snapToGo(s)
		if got := proto.Size(m); got != len(want) {
			t.Fatalf("proto.Size %d, snapEnc's length %d", got, len(want))
		}
		got, err := proto.Marshal(m)
		if err != nil || !bytes.Equal(got, want) {
			t.Fatalf("proto.Marshal %x (%v), snapEnc %x", got, err, want)
		}
		var d walpb.Snapshot
		if err := proto.Unmarshal(want, &d); err != nil {
			t.Fatalf("Unmarshal(snapEnc) failed: %v", err)
		}
		sameSnap(t, &d, s, want)
	}
}

func checkSchema(t *testing.T, fds protoreflect.FieldDescriptors, s map[protowire.Number][]protowire.Type) {
	t.Helper()
	if fds.Len() != len(s) {
		t.Fatalf("%d fields, schema %d", fds.Len(), len(s))
	}
	for i := 0; i < fds.Len(); i++ {
		fd := fds.Get(i)
		wts, ok := s[fd.Number()]
		if !ok {
			t.Fatalf("field %v not in the schema", fd.Number())
		}
		var want []protowire.Type
		switch fd.Kind() {
		case protoreflect.Uint64Kind, protoreflect.BoolKind:
			want = []protowire.Type{protowire.VarintType}
			if fd.Cardinality() == protoreflect.Repeated {
				if fd.IsPacked() {
					t.Fatalf("field %v packed", fd.Number())
				}
				want = append(want, protowire.BytesType)
			}
		case protoreflect.MessageKind:
			want = []protowire.Type{protowire.BytesType}
		default:
			t.Fatalf("field %v kind %v", fd.Number(), fd.Kind())
		}
		if !slices.Equal(wts, want) {
			t.Fatalf("field %v: schema %v, descriptor %v", fd.Number(), wts, want)
		}
	}
}

func TestSnapshotSchema(t *testing.T) {
	checkSchema(t, (&walpb.Snapshot{}).ProtoReflect().Descriptor().Fields(), walSnapSchema)
	checkSchema(t, (&raftpb.ConfState{}).ProtoReflect().Descriptor().Fields(), walCsSchema)
}
