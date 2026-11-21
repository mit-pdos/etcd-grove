package walpb

// The hard state's decoder side at adversarial inputs (wal-item3, 2026-11-21; adopted from the independent
// attack on the registration of raftpb.HardState, /shared/tmp/walitem3-attack/). hsUfWire transcribes
// UfWire.lean's ufWire (wire values at depth 10001, minimal tags, numbers in [1, 2^29)) and hsSchemaW is
// hsSchema. TestHardStateD1 decodes random byte strings (the HardState field numbers with wrong wire types,
// non-minimal tags and varints, duplicates, nested and mismatched groups, numbers 0, 19000-19999, 2^29-1,
// 2^29, truncations) and checks, on each decoded message: the decoder's post D1 at HardState (its unknown
// fields ufWire at hsSchema, its re-encoding at most twice the input), proto.Size and proto.Marshal against
// hsEnc, the round trip D2, proto.Clone and MarshalAppend. TestHardStateEncoderAllUf checks hsEncC_ok's
// premise in full: Marshal/Size/Unmarshal against hsEnc for unknown fields that are any ufWire-valid bytes
// (groups and large numbers included, which hardstate_test.go's genUFAt does not make).

import (
	"bytes"
	"math/rand"
	"testing"

	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

var hsSchemaW = map[uint64][]uint64{1: {0}, 2: {0}, 3: {0}}

// isVarint: Lean IsVarint; returns value, length
func hsReadVarint(b []byte) (uint64, int, bool) {
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

// wfields: Lean WFields d, consumes until end tag of num `grp` if grp>0; returns rest after etag
func hsWval(b []byte, d int, num, wt uint64) (int, bool) {
	switch wt {
	case 0:
		_, n, ok := hsReadVarint(b)
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
		l, n, ok := hsReadVarint(b)
		if !ok || uint64(len(b)-n) < l {
			return 0, false
		}
		return n + int(l), true
	case 3:
		if d < 1 {
			return 0, false
		}
		// body: fields at depth d-1, then etag (num,4)
		i := 0
		for {
			t, n, ok := hsReadVarint(b[i:])
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
			m, ok := hsWval(b[i+n:], d-1, tn, twt)
			if !ok {
				return 0, false
			}
			i += n + m
		}
	}
	return 0, false
}

func hsUfWire(s map[uint64][]uint64, b []byte) bool {
	for len(b) > 0 {
		t, n, ok := hsReadVarint(b)
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
		for _, w := range s[num] {
			if w == wt {
				return false
			}
		}
		m, ok := hsWval(b[n:], 10001, num, wt)
		if !ok {
			return false
		}
		b = b[n+m:]
	}
	return true
}

func hsOptVarint(b []byte, n protowire.Number, p *uint64) []byte {
	if p == nil {
		return b
	}
	b = protowire.AppendTag(b, n, protowire.VarintType)
	return protowire.AppendVarint(b, *p)
}

func hsEncG(d *raftpb.HardState) []byte {
	var b []byte
	b = hsOptVarint(b, 1, d.Term)
	b = hsOptVarint(b, 2, d.Vote)
	b = hsOptVarint(b, 3, d.Commit)
	return append(b, d.ProtoReflect().GetUnknown()...)
}

func hsAppTag(r *rand.Rand, b []byte, num uint64, wt uint64) []byte {
	t := num<<3 | wt
	b = protowire.AppendVarint(b, t)
	if r.Intn(6) == 0 { // non-minimal: add a continuation 0x80 then 0x00
		b[len(b)-1] |= 0x80
		b = append(b, 0)
	}
	return b
}

func hsGenField(r *rand.Rand, b []byte, depth int) []byte {
	nums := []uint64{1, 2, 3, 4, 5, 15, 16, 2047, 19000, 19999, 1<<29 - 1, 1 << 29, 0}
	num := nums[r.Intn(len(nums))]
	if r.Intn(3) == 0 {
		num = uint64(1 + r.Intn(5))
	}
	wt := uint64(r.Intn(8))
	if r.Intn(2) == 0 {
		wt = []uint64{0, 1, 2, 3, 5}[r.Intn(5)]
	}
	b = hsAppTag(r, b, num, wt)
	switch wt {
	case 0:
		v := []uint64{0, 1, 127, 128, 1 << 63, ^uint64(0)}[r.Intn(6)]
		b = protowire.AppendVarint(b, v)
		if r.Intn(5) == 0 {
			b[len(b)-1] |= 0x80
			b = append(b, 0)
		}
	case 1:
		b = append(b, make([]byte, 8)...)
	case 5:
		b = append(b, make([]byte, 4)...)
	case 2:
		var inner []byte
		if r.Intn(2) == 0 {
			inner = hsGenField(r, nil, depth+1)
		} else {
			inner = make([]byte, r.Intn(5))
		}
		b = protowire.AppendBytes(b, inner)
	case 3:
		if depth < 4 {
			for k := r.Intn(3); k > 0; k-- {
				b = hsGenField(r, b, depth+1)
			}
		}
		en := num
		if r.Intn(8) == 0 {
			en = num + 1
		}
		b = hsAppTag(r, b, en, 4)
	case 4:
	default:
	}
	if r.Intn(30) == 0 && len(b) > 0 {
		b = b[:r.Intn(len(b))]
	}
	return b
}

func TestHardStateD1(t *testing.T) {
	r := rand.New(rand.NewSource(7))
	decoded := 0
	for i := 0; i < 1000000; i++ {
		var bs []byte
		for k := r.Intn(5); k > 0; k-- {
			bs = hsGenField(r, bs, 0)
		}
		var d raftpb.HardState
		if err := proto.Unmarshal(bs, &d); err != nil {
			continue
		}
		decoded++
		uf := d.ProtoReflect().GetUnknown()
		if !hsUfWire(hsSchemaW, uf) {
			t.Fatalf("D1 hsUfWire fails: input %x uf %x", bs, uf)
		}
		enc := hsEncG(&d)
		if len(enc) > 2*len(bs) {
			t.Fatalf("D1 size: input %x enc %x", bs, enc)
		}
		if proto.Size(&d) != len(enc) {
			t.Fatalf("Size %d != %d", proto.Size(&d), len(enc))
		}
		m, err := proto.Marshal(&d)
		if err != nil || !bytes.Equal(m, enc) {
			t.Fatalf("Marshal %x != hsEnc %x", m, enc)
		}
		var d2 raftpb.HardState
		if err := proto.Unmarshal(enc, &d2); err != nil {
			t.Fatalf("D2 decode fails %x", enc)
		}
		if !sameOpt(d.Term, d2.Term) || !sameOpt(d.Vote, d2.Vote) || !sameOpt(d.Commit, d2.Commit) || !bytes.Equal(uf, d2.ProtoReflect().GetUnknown()) {
			t.Fatalf("D2 differs: %x", enc)
		}
		c := proto.Clone(&d).(*raftpb.HardState)
		if !sameOpt(d.Term, c.Term) || !sameOpt(d.Vote, c.Vote) || !sameOpt(d.Commit, c.Commit) || !bytes.Equal(uf, c.ProtoReflect().GetUnknown()) {
			t.Fatalf("Clone differs")
		}
		var o proto.MarshalOptions
		pre := []byte{9, 9}
		ma, err := o.MarshalAppend(pre, &d)
		if err != nil || !bytes.Equal(ma, append([]byte{9, 9}, enc...)) {
			t.Fatalf("MarshalAppend")
		}
	}
	t.Logf("decoded %d", decoded)
}

func TestHardStateEncoderAllUf(t *testing.T) {
	r := rand.New(rand.NewSource(11))
	n := 0
	for i := 0; i < 1000000; i++ {
		var uf []byte
		for k := 1 + r.Intn(3); k > 0; k-- {
			uf = hsGenField(r, uf, 0)
		}
		if !hsUfWire(hsSchemaW, uf) {
			continue
		}
		n++
		vals := []uint64{0, 1, 300, ^uint64(0)}
		var c raftpb.HardState
		if r.Intn(2) == 0 {
			v := vals[r.Intn(4)]
			c.Term = &v
		}
		if r.Intn(2) == 0 {
			v := vals[r.Intn(4)]
			c.Vote = &v
		}
		if r.Intn(2) == 0 {
			v := vals[r.Intn(4)]
			c.Commit = &v
		}
		c.ProtoReflect().SetUnknown(protoreflect.RawFields(uf))
		enc := hsEncG(&c)
		m, err := proto.Marshal(&c)
		if err != nil || !bytes.Equal(m, enc) || proto.Size(&c) != len(enc) {
			t.Fatalf("marshal %x vs %x (%v)", m, enc, err)
		}
		var d raftpb.HardState
		if err := proto.Unmarshal(enc, &d); err != nil {
			t.Fatalf("D2 decode fails %x: %v", enc, err)
		}
		if !sameOpt(d.Term, c.Term) || !sameOpt(d.Vote, c.Vote) || !sameOpt(d.Commit, c.Commit) || !bytes.Equal(uf, d.ProtoReflect().GetUnknown()) {
			t.Fatalf("D2 differs: %x", enc)
		}
	}
	t.Logf("hsUfWire-valid contents %d", n)
}
