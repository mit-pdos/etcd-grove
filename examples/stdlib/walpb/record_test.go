// Package walpb checks the Lean model of walpb.Record's wire format
// (Proof/go_etcd_io/etcd/server/v3/storage/WalPbWire.lean) and the trusted facts the registration
// of walpb.Record states over it (LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/PbRecord.lean:
// recEncC_ok, and the proto specs at the type: SizePb, MarshalPb, MarshalAppendCachedPb,
// UnmarshalPb's D1/D2) against protobuf-go (the version examples/go.mod selects) and the walpb
// package at the fork's pin.
//
// recEnc and recSize below transcribe the Lean definitions one for one. For random wire contents
// (each field's presence, zero values included; negative types; data nil, empty non-nil, short and
// long; unknown fields routed to the unknown fields at recSchema) the tests compare:
//   - proto.Marshal, and MarshalOptions{UseCachedSize: true}.MarshalAppend after proto.Size (what
//     the WAL's encode calls, encoder.go:78-91), with recEnc;
//   - proto.Size with recSize;
//   - proto.Unmarshal(recEnc c) with c itself (presence, nil versus empty data, the unknown fields
//     verbatim): the round trip D2 and the decoder view (RecC.model);
//   - the descriptor of walpb.Record with recSchema (number -> the wire types the decoder takes).
package walpb

import (
	"bytes"
	"math/rand"
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// recC is the Lean RecC.
type recC struct {
	typ  *uint64 // the int64's bits
	crc  *uint32
	data []byte // nil: absent
	uf   []byte
}

// varintEnc is the Lean varintEnc (UfWire.lean).
func varintEnc(n uint64) []byte {
	var b []byte
	for n >= 128 {
		b = append(b, byte(n%128+128))
		n /= 128
	}
	return append(b, byte(n))
}

// recEnc is the Lean recEnc.
func recEnc(c recC) []byte {
	var b []byte
	if c.typ != nil {
		b = append(b, varintEnc(1*8)...)
		b = append(b, varintEnc(*c.typ)...)
	}
	if c.crc != nil {
		b = append(b, varintEnc(2*8)...)
		b = append(b, varintEnc(uint64(*c.crc))...)
	}
	if c.data != nil {
		b = append(b, varintEnc(3*8+2)...)
		b = append(b, varintEnc(uint64(len(c.data)))...)
		b = append(b, c.data...)
	}
	return append(b, c.uf...)
}

// recSize is the Lean recSize.
func recSize(c recC) int {
	n := 0
	if c.typ != nil {
		n += 1 + len(varintEnc(*c.typ))
	}
	if c.crc != nil {
		n += 1 + len(varintEnc(uint64(*c.crc)))
	}
	if c.data != nil {
		n += 1 + len(varintEnc(uint64(len(c.data)))) + len(c.data)
	}
	return n + len(c.uf)
}

// recSchema is the Lean recSchema.
var recSchema = map[protowire.Number][]protowire.Type{
	1: {protowire.VarintType},
	2: {protowire.VarintType},
	3: {protowire.BytesType},
}

func rval(r *rand.Rand) uint64 {
	switch r.Intn(5) {
	case 0:
		return 0
	case 1:
		return uint64(r.Intn(128))
	case 2:
		return uint64(r.Intn(1 << 16))
	case 3:
		return r.Uint64()
	default:
		return uint64(-int64(r.Intn(1000) + 1)) // a negative int64
	}
}

// genUF: whole fields, each routed to the unknown fields at recSchema (an undeclared number, or a
// declared one with a wire type its decoder does not take), minimal tags.
func genUF(r *rand.Rand) []byte {
	var b []byte
	for k := r.Intn(3); k > 0; k-- {
		var num protowire.Number
		var wt protowire.Type
		for {
			num = protowire.Number(1 + r.Intn(40))
			wt = []protowire.Type{protowire.VarintType, protowire.Fixed64Type, protowire.BytesType,
				protowire.Fixed32Type}[r.Intn(4)]
			ok := true
			for _, t := range recSchema[num] {
				if t == wt {
					ok = false
				}
			}
			if ok {
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

func genRec(r *rand.Rand) recC {
	var c recC
	if r.Intn(5) != 0 {
		v := rval(r)
		c.typ = &v
	}
	if r.Intn(5) != 0 {
		v := uint32(rval(r))
		c.crc = &v
	}
	switch r.Intn(5) {
	case 0: // nil
	case 1:
		c.data = []byte{}
	case 2:
		c.data = make([]byte, 1+r.Intn(130))
		r.Read(c.data)
	case 3:
		c.data = make([]byte, 1+r.Intn(70000))
		r.Read(c.data)
	default:
		c.data = make([]byte, 1+r.Intn(10))
	}
	if r.Intn(3) == 0 {
		c.uf = genUF(r)
	}
	return c
}

func toGo(c recC) *walpb.Record {
	m := &walpb.Record{Data: c.data}
	if c.typ != nil {
		m.Type = new(int64(*c.typ))
	}
	if c.crc != nil {
		m.Crc = new(*c.crc)
	}
	if c.uf != nil {
		m.ProtoReflect().SetUnknown(protoreflect.RawFields(c.uf))
	}
	return m
}

func sameContent(t *testing.T, m *walpb.Record, c recC, enc []byte) {
	t.Helper()
	if (m.Type == nil) != (c.typ == nil) || (m.Type != nil && uint64(*m.Type) != *c.typ) {
		t.Fatalf("Type differs, encoding %x", enc)
	}
	if (m.Crc == nil) != (c.crc == nil) || (m.Crc != nil && *m.Crc != *c.crc) {
		t.Fatalf("Crc differs, encoding %x", enc)
	}
	if (m.Data == nil) != (c.data == nil) || !bytes.Equal(m.Data, c.data) {
		t.Fatalf("Data differs (nil %v, want nil %v), encoding %x", m.Data == nil, c.data == nil, enc)
	}
	if !bytes.Equal(m.ProtoReflect().GetUnknown(), c.uf) {
		t.Fatalf("unknown fields differ, encoding %x", enc)
	}
}

func TestRecordEncoder(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	const n = 200000
	buf := make([]byte, 1024*1024)
	for i := 0; i < n; i++ {
		c := genRec(r)
		want := recEnc(c)
		if len(want) != recSize(c) {
			t.Fatalf("recEnc's length %d, recSize %d", len(want), recSize(c))
		}
		m := toGo(c)
		if got := proto.Size(m); got != recSize(c) {
			t.Fatalf("proto.Size %d, recSize %d", got, recSize(c))
		}
		got, err := proto.Marshal(m)
		if err != nil || !bytes.Equal(got, want) {
			t.Fatalf("proto.Marshal %x (%v), recEnc %x", got, err, want)
		}
		// encode's path: Size, then MarshalAppend with the cached size into a 1MB buffer's [:0].
		_ = proto.Size(m)
		got2, err := proto.MarshalOptions{UseCachedSize: true}.MarshalAppend(buf[:0], m)
		if err != nil || !bytes.Equal(got2, want) {
			t.Fatalf("MarshalAppend %x (%v), recEnc %x", got2, err, want)
		}
		if len(want) <= cap(buf) && &got2[:1][0] != &buf[:1][0] {
			t.Fatalf("MarshalAppend did not append in place")
		}
		var d walpb.Record
		if err := proto.Unmarshal(want, &d); err != nil {
			t.Fatalf("Unmarshal(recEnc) failed: %v", err)
		}
		sameContent(t, &d, c, want)
	}
}

// The WAL's records (recOf): the CRC record without data, the others with data never nil.
func TestRecOf(t *testing.T) {
	crcType := uint64(4)
	var zero uint32
	c := recC{typ: &crcType, crc: &zero}
	m := &walpb.Record{Type: new(int64(4)), Crc: new(uint32(0))}
	got, _ := proto.Marshal(m)
	if !bytes.Equal(got, recEnc(c)) {
		t.Fatalf("CRC record %x, recEnc %x", got, recEnc(c))
	}
	// A snapshot record of the empty walpb.Snapshot (Create's SaveSnapshot): Marshal gives a
	// non-nil empty slice, so the record's Data is present with length 0.
	b, _ := proto.Marshal(&walpb.Snapshot{})
	if b == nil || len(b) != 0 {
		t.Fatalf("Marshal(&walpb.Snapshot{}) = %#v", b)
	}
	snapType := uint64(5)
	c = recC{typ: &snapType, crc: &zero, data: []byte{}}
	got, _ = proto.Marshal(&walpb.Record{Type: new(int64(5)), Crc: new(uint32(0)), Data: b})
	if !bytes.Equal(got, recEnc(c)) {
		t.Fatalf("snapshot record %x, recEnc %x", got, recEnc(c))
	}
}

func TestRecordSchema(t *testing.T) {
	fds := (&walpb.Record{}).ProtoReflect().Descriptor().Fields()
	if fds.Len() != len(recSchema) {
		t.Fatalf("%d fields, schema %d", fds.Len(), len(recSchema))
	}
	for i := 0; i < fds.Len(); i++ {
		fd := fds.Get(i)
		wts, ok := recSchema[fd.Number()]
		if !ok || fd.Cardinality() == protoreflect.Repeated {
			t.Fatalf("field %v not in the schema", fd.Number())
		}
		var want protowire.Type
		switch fd.Kind() {
		case protoreflect.Int64Kind, protoreflect.Uint32Kind:
			want = protowire.VarintType
		case protoreflect.BytesKind:
			want = protowire.BytesType
		default:
			t.Fatalf("field %v kind %v", fd.Number(), fd.Kind())
		}
		if len(wts) != 1 || wts[0] != want {
			t.Fatalf("field %v: schema %v, descriptor %v", fd.Number(), wts, want)
		}
	}
}
