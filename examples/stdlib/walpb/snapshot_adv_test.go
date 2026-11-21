package walpb

// Axiom review (snapEncC_ok, pbSnapC_reg, pbRecordC_reg, proto.MarshalAppendCachedRecord.wp_proof),
// 2026-11-21: the claims at inputs examples/stdlib/walpb's generators do not make (unknown fields with
// groups, deep groups, large and reserved numbers, non-minimal values and inner tags, known numbers with
// wrong wire types, at both levels of walpb.Snapshot), and the generic specs the registration enrolls
// walpb.Snapshot in (Size, Marshal, MarshalAppend, Unmarshal D1/D2, Clone).

import (
	"bytes"
	"math/rand"
	"slices"
	"testing"
	"unsafe"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

var snapSchemaAdv = map[uint64][]uint64{1: {0}, 2: {0}, 3: {2}}
var csSchemaAdv = map[uint64][]uint64{1: {0, 2}, 2: {0, 2}, 3: {0, 2}, 4: {0, 2}, 5: {0}}
var recSchemaAdv = map[uint64][]uint64{1: {0}, 2: {0}, 3: {2}}

// ---- Lean ufWire, transcribed (as hardstate_adv_test.go) ----

func readVarint(b []byte) (uint64, int, bool) {
	var v uint64
	for i := 0; i < len(b) && i < 10; i++ {
		x := uint64(b[i] & 0x7f)
		if i == 9 && b[i] > 1 {
			return 0, 0, false
		}
		v |= x << (7 * i)
		if b[i] < 128 {
			return v, i + 1, true
		}
	}
	return 0, 0, false
}

func wval(b []byte, d int, num, wt uint64) (int, bool) {
	switch wt {
	case 0:
		_, n, ok := readVarint(b)
		return n, ok
	case 1:
		if len(b) < 8 {
			return 0, false
		}
		return 8, true
	case 5:
		if len(b) < 4 {
			return 0, false
		}
		return 4, true
	case 2:
		l, n, ok := readVarint(b)
		if !ok || uint64(len(b)-n) < l {
			return 0, false
		}
		return n + int(l), true
	case 3:
		if d < 1 {
			return 0, false
		}
		i := 0
		for {
			t, n, ok := readVarint(b[i:])
			if !ok {
				return 0, false
			}
			tn, twt := t>>3, t&7
			if tn < 1 || tn >= 1<<31 {
				return 0, false
			}
			if twt == 4 {
				if tn != num {
					return 0, false
				}
				return i + n, true
			}
			m, ok := wval(b[i+n:], d-1, tn, twt)
			if !ok {
				return 0, false
			}
			i += n + m
		}
	}
	return 0, false
}

func ufWire(s map[uint64][]uint64, b []byte) bool {
	for len(b) > 0 {
		t, n, ok := readVarint(b)
		if !ok {
			return false
		}
		num, wt := t>>3, t&7
		if num < 1 || num >= 1<<29 {
			return false
		}
		if !bytes.Equal(b[:n], protowire.AppendVarint(nil, t)) {
			return false
		}
		if slices.Contains(s[num], wt) {
			return false
		}
		m, ok := wval(b[n:], 10001, num, wt)
		if !ok {
			return false
		}
		b = b[n+m:]
	}
	return true
}

// ---- a generator of ufWire-valid unknown fields (groups, large numbers, non-minimal values) ----

func appNonMinVarint(r *rand.Rand, b []byte, v uint64) []byte {
	b = protowire.AppendVarint(b, v)
	if r.Intn(4) == 0 && len(protowire.AppendVarint(nil, v)) < 10 {
		b[len(b)-1] |= 0x80
		b = append(b, 0)
	}
	return b
}

var bigNums = []uint64{1, 2, 3, 4, 5, 6, 15, 16, 2047, 19000, 19500, 19999, 1<<29 - 1}

func genVal(r *rand.Rand, b []byte, num, wt uint64, depth int, inner bool) []byte {
	switch wt {
	case 0:
		v := []uint64{0, 1, 127, 128, 1 << 63, ^uint64(0), r.Uint64()}[r.Intn(7)]
		b = appNonMinVarint(r, b, v)
	case 1:
		x := make([]byte, 8)
		r.Read(x)
		b = append(b, x...)
	case 5:
		x := make([]byte, 4)
		r.Read(x)
		b = append(b, x...)
	case 2:
		x := make([]byte, r.Intn(6))
		r.Read(x)
		b = protowire.AppendBytes(b, x)
	case 3:
		if depth < 4 {
			for k := r.Intn(3); k > 0; k-- {
				b = genInner(r, b, depth+1)
			}
		}
		// end tag: inside a group, kept verbatim, possibly non-minimal
		b = appNonMinVarint(r, b, num<<3|4)
	}
	return b
}

func genInner(r *rand.Rand, b []byte, depth int) []byte {
	num := bigNums[r.Intn(len(bigNums))]
	if r.Intn(5) == 0 {
		num = 1<<31 - 1 // allowed inside groups
	}
	wt := []uint64{0, 1, 2, 3, 5}[r.Intn(5)]
	b = appNonMinVarint(r, b, num<<3|wt)
	return genVal(r, b, num, wt, depth, true)
}

func genUFAdv(r *rand.Rand, s map[uint64][]uint64) []byte {
	var b []byte
	for k := r.Intn(4); k > 0; k-- {
		var num, wt uint64
		for {
			num = bigNums[r.Intn(len(bigNums))]
			wt = []uint64{0, 1, 2, 3, 5}[r.Intn(5)]
			if !slices.Contains(s[num], wt) {
				break
			}
		}
		b = protowire.AppendVarint(b, num<<3|wt) // minimal outer tag
		b = genVal(r, b, num, wt, 0, false)
	}
	return b
}

// ---- Lean snapEncAdv, transcribed ----

type csCAdv struct {
	lists     [4][]uint64
	autoLeave *bool
	uf        []byte
}
type snapCAdv struct {
	index, term *uint64
	cs          *csCAdv
	uf          []byte
}

func optV(b []byte, num uint64, v *uint64) []byte {
	if v == nil {
		return b
	}
	b = protowire.AppendVarint(b, num*8)
	return protowire.AppendVarint(b, *v)
}

func csEncAdv(c csCAdv) []byte {
	var b []byte
	for i, l := range c.lists {
		for _, v := range l {
			b = protowire.AppendVarint(b, uint64(i+1)*8)
			b = protowire.AppendVarint(b, v)
		}
	}
	if c.autoLeave != nil {
		v := uint64(0)
		if *c.autoLeave {
			v = 1
		}
		b = optV(b, 5, &v)
	}
	return append(b, c.uf...)
}

func snapEncAdv(s snapCAdv) []byte {
	var b []byte
	b = optV(b, 1, s.index)
	b = optV(b, 2, s.term)
	if s.cs != nil {
		b = protowire.AppendVarint(b, 3*8+2)
		b = protowire.AppendBytes(b, csEncAdv(*s.cs))
	}
	return append(b, s.uf...)
}

func rv(r *rand.Rand) uint64 {
	return []uint64{0, 1, 127, 128, 1 << 32, 1 << 63, ^uint64(0), r.Uint64()}[r.Intn(8)]
}

func genSnapAdv(r *rand.Rand) snapCAdv {
	var s snapCAdv
	if r.Intn(4) != 0 {
		v := rv(r)
		s.index = &v
	}
	if r.Intn(4) != 0 {
		v := rv(r)
		s.term = &v
	}
	if r.Intn(4) != 0 {
		c := &csCAdv{}
		for i := range c.lists {
			for k := r.Intn(4); k > 0; k-- {
				c.lists[i] = append(c.lists[i], rv(r))
			}
		}
		if k := r.Intn(3); k > 0 {
			v := k == 2
			c.autoLeave = &v
		}
		c.uf = genUFAdv(r, csSchemaAdv)
		s.cs = c
	}
	s.uf = genUFAdv(r, snapSchemaAdv)
	return s
}

func toGoAdv(s snapCAdv) *walpb.Snapshot {
	m := &walpb.Snapshot{Index: s.index, Term: s.term}
	if s.cs != nil {
		c := &raftpb.ConfState{Voters: s.cs.lists[0], Learners: s.cs.lists[1],
			VotersOutgoing: s.cs.lists[2], LearnersNext: s.cs.lists[3], AutoLeave: s.cs.autoLeave}
		if len(s.cs.uf) > 0 {
			c.ProtoReflect().SetUnknown(protoreflect.RawFields(s.cs.uf))
		}
		m.ConfState = c
	}
	if len(s.uf) > 0 {
		m.ProtoReflect().SetUnknown(protoreflect.RawFields(s.uf))
	}
	return m
}

func fromGo(m *walpb.Snapshot) snapCAdv {
	s := snapCAdv{index: m.Index, term: m.Term, uf: m.ProtoReflect().GetUnknown()}
	if c := m.ConfState; c != nil {
		s.cs = &csCAdv{lists: [4][]uint64{c.Voters, c.Learners, c.VotersOutgoing, c.LearnersNext},
			autoLeave: c.AutoLeave, uf: c.ProtoReflect().GetUnknown()}
	}
	return s
}

func eqOpt[T comparable](a, b *T) bool { return (a == nil) == (b == nil) && (a == nil || *a == *b) }

func sameC(a, b snapCAdv) bool {
	if !eqOpt(a.index, b.index) || !eqOpt(a.term, b.term) || !bytes.Equal(a.uf, b.uf) ||
		(a.cs == nil) != (b.cs == nil) {
		return false
	}
	if a.cs == nil {
		return true
	}
	for i := range a.cs.lists {
		if !slices.Equal(a.cs.lists[i], b.cs.lists[i]) {
			return false
		}
	}
	return eqOpt(a.cs.autoLeave, b.cs.autoLeave) && bytes.Equal(a.cs.uf, b.cs.uf)
}

// snapEncC_ok in full premise, and what the registration enrolls Snapshot in (Size, Marshal,
// MarshalAppend with zero options, Unmarshal D2, Clone).
func TestSnapshotEncoderAdversarialUF(t *testing.T) {
	r := rand.New(rand.NewSource(7))
	groups := 0
	for i := 0; i < 300000; i++ {
		s := genSnapAdv(r)
		if !ufWire(snapSchemaAdv, s.uf) || (s.cs != nil && !ufWire(csSchemaAdv, s.cs.uf)) {
			t.Fatalf("generator: not ufWire")
		}
		if bytes.Contains(s.uf, []byte{0x04}) {
			groups++
		}
		want := snapEncAdv(s)
		m := toGoAdv(s)
		if got := proto.Size(m); got != len(want) {
			t.Fatalf("Size %d, snapEncAdv %d (%x)", got, len(want), want)
		}
		got, err := proto.Marshal(m)
		if err != nil || !bytes.Equal(got, want) {
			t.Fatalf("Marshal %x (%v), snapEncAdv %x", got, err, want)
		}
		pre := []byte{1, 2, 3}
		ga, err := proto.MarshalOptions{}.MarshalAppend(pre, m)
		if err != nil || !bytes.Equal(ga, append([]byte{1, 2, 3}, want...)) {
			t.Fatalf("MarshalAppend %x (%v)", ga, err)
		}
		var d walpb.Snapshot
		if err := proto.Unmarshal(want, &d); err != nil {
			t.Fatalf("Unmarshal(snapEncAdv) %x: %v", want, err)
		}
		if !sameC(fromGo(&d), s) {
			t.Fatalf("round trip differs at %x", want)
		}
		cl := proto.Clone(m).(*walpb.Snapshot)
		if !sameC(fromGo(cl), s) {
			t.Fatalf("Clone differs at %x", want)
		}
	}
	t.Logf("%d of 300000 with an unknown group-ish byte", groups)
}

// The depth bound: WVal 10001 at both levels (the ConfState's unknown fields are parsed with a fresh
// limit, protowire.ConsumeFieldValue, though the ConfState is one message deeper).
func deepGroup(n int) []byte {
	var b []byte
	for i := 0; i < n; i++ {
		b = protowire.AppendTag(b, 7, protowire.StartGroupType)
	}
	for i := 0; i < n; i++ {
		b = protowire.AppendTag(b, 7, protowire.EndGroupType)
	}
	return b
}

func TestSnapshotDeepGroups(t *testing.T) {
	for _, n := range []int{10001, 10002} {
		for lvl := 0; lvl < 2; lvl++ {
			s := snapCAdv{}
			u := deepGroup(n)
			if lvl == 0 {
				s.uf = u
			} else {
				s.cs = &csCAdv{uf: u}
			}
			sch := snapSchemaAdv
			if lvl == 1 {
				sch = csSchemaAdv
			}
			var d walpb.Snapshot
			err := proto.Unmarshal(snapEncAdv(s), &d)
			t.Logf("depth %d level %d: ufWire %v, Unmarshal err %v", n, lvl, ufWire(sch, u), err)
			if ufWire(sch, u) != (err == nil) {
				t.Fatalf("ufWire and Go disagree")
			}
			if err == nil {
				if !sameC(fromGo(&d), s) {
					t.Fatalf("round trip differs")
				}
				if got, _ := proto.Marshal(toGoAdv(s)); !bytes.Equal(got, snapEncAdv(s)) {
					t.Fatalf("Marshal differs")
				}
			}
		}
	}
}

// D1 at Snapshot (what UnmarshalPb.spec claims of any successful decode, now that the registration
// enrolls the type): decoded unknown fields ufWire at both levels, size <= 2 * input, the re-encoding is
// snapEncAdv of the decoded content, and decoding it gives that content back.
func genRaw(r *rand.Rand, b []byte, depth int, conf bool) []byte {
	nums := []uint64{1, 2, 3, 3, 3, 4, 5, 15, 19000, 1<<29 - 1, 1 << 29, 0}
	num := nums[r.Intn(len(nums))]
	wt := uint64(r.Intn(8))
	if r.Intn(2) == 0 {
		wt = []uint64{0, 1, 2, 3, 5}[r.Intn(5)]
	}
	if !conf && num == 3 && r.Intn(2) == 0 {
		wt = 2
	}
	t := num<<3 | wt
	b = protowire.AppendVarint(b, t)
	if r.Intn(6) == 0 {
		b[len(b)-1] |= 0x80
		b = append(b, 0)
	}
	switch wt {
	case 0:
		b = appNonMinVarint(r, b, rv(r))
	case 1:
		b = append(b, make([]byte, 8)...)
	case 5:
		b = append(b, make([]byte, 4)...)
	case 2:
		var inner []byte
		if !conf && num == 3 && depth == 0 {
			for k := r.Intn(5); k > 0; k-- {
				inner = genRaw(r, inner, depth+1, true)
			}
		} else if conf && num <= 4 && r.Intn(2) == 0 {
			for k := r.Intn(6); k > 0; k-- {
				inner = protowire.AppendVarint(inner, rv(r)) // packed
			}
		} else {
			inner = make([]byte, r.Intn(4))
		}
		b = protowire.AppendBytes(b, inner)
	case 3:
		if depth < 4 {
			for k := r.Intn(3); k > 0; k-- {
				b = genRaw(r, b, depth+1, conf)
			}
		}
		en := num
		if r.Intn(10) == 0 {
			en++
		}
		b = protowire.AppendVarint(b, en<<3|4)
	}
	if r.Intn(40) == 0 && len(b) > 0 {
		b = b[:r.Intn(len(b))]
	}
	return b
}

func TestSnapshotD1(t *testing.T) {
	r := rand.New(rand.NewSource(11))
	ok := 0
	for i := 0; i < 1000000; i++ {
		var in []byte
		for k := 1 + r.Intn(5); k > 0; k-- {
			in = genRaw(r, in, 0, false)
		}
		var d walpb.Snapshot
		if proto.Unmarshal(in, &d) != nil {
			continue
		}
		ok++
		c := fromGo(&d)
		if !ufWire(snapSchemaAdv, c.uf) || (c.cs != nil && !ufWire(csSchemaAdv, c.cs.uf)) {
			t.Fatalf("decoded unknown fields not ufWire, input %x", in)
		}
		enc := snapEncAdv(c)
		if len(enc) > 2*len(in) {
			t.Fatalf("size %d > 2*%d, input %x", len(enc), len(in), in)
		}
		if got, err := proto.Marshal(&d); err != nil || !bytes.Equal(got, enc) {
			t.Fatalf("Marshal of decoded != snapEncAdv, input %x", in)
		}
		var d2 walpb.Snapshot
		if err := proto.Unmarshal(enc, &d2); err != nil || !sameC(fromGo(&d2), c) {
			t.Fatalf("D2 fails, input %x", in)
		}
	}
	t.Logf("%d of 1000000 decoded", ok)
}

// ---- walpb.Record: MarshalAppend with the cached size, adversarial unknown fields ----

func arrAdv(b []byte) unsafe.Pointer { return unsafe.Pointer(unsafe.SliceData(b)) }

func TestRecordMarshalAppendCachedAdv(t *testing.T) {
	r := rand.New(rand.NewSource(5))
	for i := 0; i < 200000; i++ {
		m := &walpb.Record{}
		if r.Intn(4) != 0 {
			v := int64(rv(r))
			m.Type = &v
		}
		if r.Intn(4) != 0 {
			v := uint32(rv(r))
			m.Crc = &v
		}
		switch r.Intn(3) {
		case 1:
			m.Data = []byte{}
		case 2:
			m.Data = make([]byte, r.Intn(40))
			r.Read(m.Data)
		}
		uf := genUFAdv(r, recSchemaAdv)
		if len(uf) > 0 {
			m.ProtoReflect().SetUnknown(protoreflect.RawFields(uf))
		}
		var want []byte
		if m.Type != nil {
			want = optV(want, 1, func() *uint64 { x := uint64(*m.Type); return &x }())
		}
		if m.Crc != nil {
			want = optV(want, 2, func() *uint64 { x := uint64(*m.Crc); return &x }())
		}
		if m.Data != nil {
			want = protowire.AppendVarint(want, 3*8+2)
			want = protowire.AppendBytes(want, m.Data)
		}
		want = append(want, uf...)
		{ // recEncC_ok's round trip at adversarial unknown fields (the registration's encoder)
			var d walpb.Record
			if err := proto.Unmarshal(want, &d); err != nil || !eqOpt(d.Type, m.Type) || !eqOpt(d.Crc, m.Crc) ||
				(d.Data == nil) != (m.Data == nil) || !bytes.Equal(d.Data, m.Data) ||
				!bytes.Equal(d.ProtoReflect().GetUnknown(), uf) {
				t.Fatalf("Record round trip differs at %x (%v)", want, err)
			}
		}
		// cache: fresh, stale-small, stale-large, or none
		switch r.Intn(4) {
		case 0:
			_ = proto.Size(m)
		case 1: // stale small: size of a smaller record, then restore
			d := m.Data
			m.Data = nil
			_ = proto.Size(m)
			m.Data = d
		case 2: // stale large
			d := m.Data
			m.Data = make([]byte, 5000)
			_ = proto.Size(m)
			m.Data = d
		}
		l := r.Intn(8)
		b := make([]byte, l, l+r.Intn(len(want)+8))
		r.Read(b)
		prefix := append([]byte(nil), b...)
		got, err := proto.MarshalOptions{UseCachedSize: true}.MarshalAppend(b, m)
		if err != nil || !bytes.Equal(got, append(prefix, want...)) {
			t.Fatalf("MarshalAppend %x (%v) want %x++%x", got, err, prefix, want)
		}
		if cap(b) > 0 && arrAdv(got) == arrAdv(b) {
			if cap(got) != cap(b) {
				t.Fatalf("in place, other cap")
			}
			continue
		}
		if !bytes.Equal(b, prefix) {
			t.Fatalf("b's prefix changed")
		}
		saved := append([]byte(nil), got...)
		full := b[:cap(b)]
		for j := range full {
			full[j] ^= 0xff
		}
		if !bytes.Equal(got, saved) {
			t.Fatalf("fresh result shares b's array")
		}
	}
}
