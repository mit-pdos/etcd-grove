package pbwire

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"math"
	"math/rand"
	"os"
	"reflect"
	"sort"
	"strings"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/pbwire/xpb"
	"go.etcd.io/etcd/api/v3/authpb"
	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/server/v3/lease/leasepb"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
	"models.lab/pbdesc"
)

// The Lean module the test writes (relative to this package's directory).
const leanPath = "../../Proof/google_golang_org/protobuf/proto/PbWireVectors.lean"

// The root message types: the vectors are of these; the descriptors are of their closure.
var roots = []proto.Message{
	&raftpb.Entry{}, &raftpb.Message{}, &raftpb.HardState{}, &raftpb.ConfState{},
	&raftpb.ConfChange{}, &raftpb.ConfChangeV2{}, &raftpb.Snapshot{},
	&walpb.Record{}, &walpb.Snapshot{},
	&etcdserverpb.RangeRequest{}, &etcdserverpb.RangeResponse{}, &etcdserverpb.PutRequest{},
	&etcdserverpb.DeleteRangeRequest{}, &etcdserverpb.TxnRequest{}, &etcdserverpb.TxnResponse{},
	&etcdserverpb.WatchRequest{}, &etcdserverpb.WatchResponse{}, &etcdserverpb.Member{},
	&etcdserverpb.LeaseGrantRequest{}, &mvccpb.KeyValue{}, &leasepb.Lease{},
	&authpb.User{}, &authpb.Role{},
	&xpb.Kinds{},
}

// Per root type: random messages (encode vectors), and decode inputs derived from them.
const (
	encPerType  = 10
	mutPerType  = 8
	wirePerType = 12
)

// ---- Lean rendering ----

func leanHex(b []byte) string { return fmt.Sprintf("(hex %q)", hex.EncodeToString(b)) }

func leanInt(x int64) string {
	if x < 0 {
		return fmt.Sprintf(".int (%d)", x)
	}
	return fmt.Sprintf(".int %d", x)
}

func leanScalar(fd protoreflect.FieldDescriptor, v protoreflect.Value) string {
	switch fd.Kind() {
	case protoreflect.BoolKind:
		return fmt.Sprintf(".bool %t", v.Bool())
	case protoreflect.EnumKind:
		return leanInt(int64(v.Enum()))
	case protoreflect.Int32Kind, protoreflect.Sint32Kind, protoreflect.Sfixed32Kind,
		protoreflect.Int64Kind, protoreflect.Sint64Kind, protoreflect.Sfixed64Kind:
		return leanInt(v.Int())
	case protoreflect.Uint32Kind, protoreflect.Fixed32Kind, protoreflect.Uint64Kind, protoreflect.Fixed64Kind:
		return fmt.Sprintf(".int %d", v.Uint())
	case protoreflect.StringKind:
		return ".bytes " + leanHex([]byte(v.String()))
	case protoreflect.BytesKind:
		return ".bytes " + leanHex(v.Bytes())
	case protoreflect.MessageKind:
		return leanMsg(v.Message())
	}
	panic(fmt.Sprintf("%s: kind %v not covered by the Lean semantics", fd.FullName(), fd.Kind()))
}

// leanMsg is the Lean `Value` of a message: its populated fields by increasing number (what
// protoreflect's Range reports: an implicit-presence field at zero is not populated), and its
// unknown fields' bytes.
func leanMsg(m protoreflect.Message) string {
	type fv struct {
		fd protoreflect.FieldDescriptor
		v  protoreflect.Value
	}
	var fs []fv
	m.Range(func(fd protoreflect.FieldDescriptor, v protoreflect.Value) bool {
		fs = append(fs, fv{fd, v})
		return true
	})
	sort.Slice(fs, func(i, j int) bool { return fs[i].fd.Number() < fs[j].fd.Number() })
	var parts []string
	for _, f := range fs {
		var s string
		if f.fd.IsMap() {
			panic(fmt.Sprintf("%s: maps are not covered", f.fd.FullName()))
		} else if f.fd.IsList() {
			l := f.v.List()
			var es []string
			for i := 0; i < l.Len(); i++ {
				es = append(es, leanScalar(f.fd, l.Get(i)))
			}
			s = ".list [" + strings.Join(es, ", ") + "]"
		} else {
			s = leanScalar(f.fd, f.v)
		}
		parts = append(parts, fmt.Sprintf("(%d, %s)", f.fd.Number(), s))
	}
	return fmt.Sprintf("(.msg [%s] %s)", strings.Join(parts, ", "), leanHex(m.GetUnknown()))
}

var leanKinds = map[string]string{
	"int32": ".int32", "int64": ".int64", "uint32": ".uint32", "uint64": ".uint64",
	"sint32": ".sint32", "sint64": ".sint64", "bool": ".bool", "enum": ".enum",
	"fixed32": ".fixed32", "fixed64": ".fixed64", "sfixed32": ".sfixed32", "sfixed64": ".sfixed64",
	"string": ".string", "bytes": ".bytes",
}

// leanDesc renders pbdesc's dump as the Lean descriptor (`PbWire.Desc`), refusing what the
// semantics does not cover.
func leanDesc(d *pbdesc.Dump) (string, error) {
	var ms []string
	for _, m := range d.Messages {
		if m.MapEntry || m.MessageSet || m.ExtensionRanges > 0 {
			return "", fmt.Errorf("%s: map entry, MessageSet or extensions", m.FullName)
		}
		var fs []string
		for _, f := range m.Fields {
			if f.IsMap || f.IsWeak || f.Lazy || f.Cardinality == "required" {
				return "", fmt.Errorf("%s.%s: map, weak, lazy or required", m.FullName, f.Name)
			}
			var kind string
			if f.Kind == "message" {
				kind = fmt.Sprintf("(.message %q)", f.Message)
			} else if k, ok := leanKinds[f.Kind]; ok {
				kind = k
			} else {
				return "", fmt.Errorf("%s.%s: kind %s not covered", m.FullName, f.Name, f.Kind)
			}
			card := ".implicit"
			if f.Cardinality == "repeated" {
				card = ".repeated"
			} else if f.HasPresence {
				card = ".explicit"
			}
			oneof := "none"
			if f.Oneof != "" && !f.SyntheticOneof {
				oneof = fmt.Sprintf("some %q", f.Oneof)
			}
			fs = append(fs, fmt.Sprintf("{ name := %q, num := %d, kind := %s, card := %s, packed := %t, oneof := %s, utf8 := %t }",
				f.Name, f.Number, kind, card, f.Packed, oneof, f.EnforceUTF8))
		}
		ms = append(ms, fmt.Sprintf("  { name := %q, fields :=\n    [%s] }", m.FullName, strings.Join(fs, ",\n     ")))
	}
	return "[\n" + strings.Join(ms, ",\n") + " ]", nil
}

// ---- random messages ----

var ints32 = []int64{0, 1, -1, 2, 63, 64, 127, 128, 300, 16383, 16384, math.MaxInt32, math.MinInt32, -129}
var ints64 = []int64{0, 1, -1, 127, 128, 1 << 35, math.MaxInt64, math.MinInt64, -300, math.MaxInt32 + 1}
var uints32 = []uint64{0, 1, 127, 128, 255, 256, 1 << 21, math.MaxUint32, math.MaxUint32 - 1}
var uints64 = []uint64{0, 1, 127, 128, 1 << 32, 1<<63 - 1, 1 << 63, math.MaxUint64, 300}
var strs = []string{"", "a", "key", "é", "€x", "😀", "\x00", "hello world"}
var badStrs = []string{"\xff", "\xed\xa0\x80", "\xc0\xaf", "\xf4\x90\x80\x80", "a\xe2\x82"}

type gen struct {
	r *rand.Rand
	// allow invalid UTF-8 in validated strings
	badUTF8 bool
}

func (g *gen) pick(n int) int { return g.r.Intn(n) }

func (g *gen) scalar(fd protoreflect.FieldDescriptor) protoreflect.Value {
	switch fd.Kind() {
	case protoreflect.BoolKind:
		return protoreflect.ValueOfBool(g.pick(2) == 1)
	case protoreflect.EnumKind:
		vals := fd.Enum().Values()
		if g.pick(4) == 0 {
			return protoreflect.ValueOfEnum(protoreflect.EnumNumber(int32(ints32[g.pick(len(ints32))])))
		}
		return protoreflect.ValueOfEnum(vals.Get(g.pick(vals.Len())).Number())
	case protoreflect.Int32Kind, protoreflect.Sint32Kind, protoreflect.Sfixed32Kind:
		if g.pick(3) == 0 {
			return protoreflect.ValueOfInt32(int32(g.r.Uint32()))
		}
		return protoreflect.ValueOfInt32(int32(ints32[g.pick(len(ints32))]))
	case protoreflect.Int64Kind, protoreflect.Sint64Kind, protoreflect.Sfixed64Kind:
		if g.pick(3) == 0 {
			return protoreflect.ValueOfInt64(int64(g.r.Uint64()))
		}
		return protoreflect.ValueOfInt64(ints64[g.pick(len(ints64))])
	case protoreflect.Uint32Kind, protoreflect.Fixed32Kind:
		if g.pick(3) == 0 {
			return protoreflect.ValueOfUint32(g.r.Uint32())
		}
		return protoreflect.ValueOfUint32(uint32(uints32[g.pick(len(uints32))]))
	case protoreflect.Uint64Kind, protoreflect.Fixed64Kind:
		if g.pick(3) == 0 {
			return protoreflect.ValueOfUint64(g.r.Uint64() >> uint(g.pick(64)))
		}
		return protoreflect.ValueOfUint64(uints64[g.pick(len(uints64))])
	case protoreflect.StringKind:
		if g.badUTF8 && g.pick(3) == 0 {
			return protoreflect.ValueOfString(badStrs[g.pick(len(badStrs))])
		}
		return protoreflect.ValueOfString(strs[g.pick(len(strs))])
	case protoreflect.BytesKind:
		b := make([]byte, g.pick(6))
		g.r.Read(b)
		return protoreflect.ValueOfBytes(b)
	}
	panic(fmt.Sprintf("%s: kind %v", fd.FullName(), fd.Kind()))
}

// unknownField is one well-formed field numbered `num` of a random wire type (a group with a
// nested field and group sometimes).
func (g *gen) unknownField(num protowire.Number) []byte {
	var b []byte
	switch g.pick(5) {
	case 0:
		b = protowire.AppendTag(b, num, protowire.VarintType)
		b = protowire.AppendVarint(b, uints64[g.pick(len(uints64))])
	case 1:
		b = protowire.AppendTag(b, num, protowire.Fixed64Type)
		b = protowire.AppendFixed64(b, g.r.Uint64())
	case 2:
		b = protowire.AppendTag(b, num, protowire.BytesType)
		x := make([]byte, g.pick(4))
		g.r.Read(x)
		b = protowire.AppendBytes(b, x)
	case 3:
		b = protowire.AppendTag(b, num, protowire.Fixed32Type)
		b = protowire.AppendFixed32(b, g.r.Uint32())
	case 4:
		b = protowire.AppendTag(b, num, protowire.StartGroupType)
		b = protowire.AppendTag(b, 1, protowire.VarintType)
		b = protowire.AppendVarint(b, 5)
		if g.pick(2) == 0 {
			b = protowire.AppendTag(b, 2, protowire.StartGroupType)
			b = protowire.AppendTag(b, 2, protowire.EndGroupType)
		}
		b = protowire.AppendTag(b, num, protowire.EndGroupType)
	}
	return b
}

// unknownNum is a field number the message does not declare.
func (g *gen) unknownNum(md protoreflect.MessageDescriptor) protowire.Number {
	for {
		var n protowire.Number
		switch g.pick(3) {
		case 0:
			n = protowire.Number(1 + g.pick(40))
		case 1:
			n = protowire.Number(100 + g.pick(3000))
		default:
			n = protowire.Number(1 << 28)
		}
		if md.Fields().ByNumber(n) == nil {
			return n
		}
	}
}

func (g *gen) fill(m protoreflect.Message, depth int, unknowns bool) {
	md := m.Descriptor()
	fields := md.Fields()
	for i := 0; i < fields.Len(); i++ {
		fd := fields.Get(i)
		if od := fd.ContainingOneof(); od != nil && !od.IsSynthetic() {
			continue
		}
		if g.pick(3) == 0 {
			continue
		}
		g.setField(m, fd, depth, unknowns)
	}
	for i := 0; i < md.Oneofs().Len(); i++ {
		od := md.Oneofs().Get(i)
		if od.IsSynthetic() || g.pick(3) == 0 {
			continue
		}
		g.setField(m, od.Fields().Get(g.pick(od.Fields().Len())), depth, unknowns)
	}
	if unknowns && g.pick(4) == 0 {
		var u []byte
		for k := 0; k < 1+g.pick(2); k++ {
			u = append(u, g.unknownField(g.unknownNum(md))...)
		}
		m.SetUnknown(u)
	}
}

func (g *gen) setField(m protoreflect.Message, fd protoreflect.FieldDescriptor, depth int, unknowns bool) {
	switch {
	case fd.IsList():
		n := g.pick(4)
		if fd.Kind() == protoreflect.MessageKind && depth <= 0 {
			return
		}
		l := m.Mutable(fd).List()
		for k := 0; k < n; k++ {
			if fd.Kind() == protoreflect.MessageKind {
				e := l.NewElement()
				g.fill(e.Message(), depth-1, unknowns)
				l.Append(e)
			} else {
				l.Append(g.scalar(fd))
			}
		}
	case fd.Kind() == protoreflect.MessageKind:
		if depth <= 0 {
			return
		}
		g.fill(m.Mutable(fd).Message(), depth-1, unknowns)
	default:
		m.Set(fd, g.scalar(fd))
	}
}

func hasUnknown(m protoreflect.Message) bool {
	if len(m.GetUnknown()) > 0 {
		return true
	}
	found := false
	m.Range(func(fd protoreflect.FieldDescriptor, v protoreflect.Value) bool {
		if fd.Kind() != protoreflect.MessageKind {
			return true
		}
		if fd.IsList() {
			for i := 0; i < v.List().Len(); i++ {
				if hasUnknown(v.List().Get(i).Message()) {
					found = true
				}
			}
		} else if hasUnknown(v.Message()) {
			found = true
		}
		return !found
	})
	return found
}

// pbgenMarshal is pbgen's codec, or ok = false for a type outside it.
func pbgenMarshal(m proto.Message) (b []byte, err error, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			ok = false
		}
	}()
	b, err = pbMarshal(m)
	return b, err, true
}

// ---- crafted wire inputs ----

func (g *gen) wireInput(md protoreflect.MessageDescriptor) []byte {
	var b []byte
	num := g.unknownNum(md)
	if fs := md.Fields(); fs.Len() > 0 && g.pick(4) != 0 {
		num = fs.Get(g.pick(fs.Len())).Number()
	}
	wt := protowire.Type(g.pick(8))
	// a tag, minimal or not
	if g.pick(5) == 0 {
		v := protowire.EncodeTag(num, wt)
		b = append(b, byte(v&0x7f|0x80))
		b = protowire.AppendVarint(b, v>>7)
	} else {
		b = protowire.AppendVarint(b, protowire.EncodeTag(num, wt))
	}
	switch wt {
	case protowire.VarintType:
		switch g.pick(4) {
		case 0:
			b = append(b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, byte(g.pick(3))) // 10 bytes, 10th 0..2
		case 1:
			b = append(b, 0x80, 0x00) // non-minimal 0
		default:
			b = protowire.AppendVarint(b, uints64[g.pick(len(uints64))])
		}
	case protowire.Fixed64Type:
		b = protowire.AppendFixed64(b, g.r.Uint64())
	case protowire.Fixed32Type:
		b = protowire.AppendFixed32(b, g.r.Uint32())
	case protowire.BytesType:
		var x []byte
		switch g.pick(4) {
		case 0: // packed varints
			for k := 0; k < g.pick(4); k++ {
				x = protowire.AppendVarint(x, uints64[g.pick(len(uints64))])
			}
		case 1: // a cut varint
			x = []byte{0x01, 0x80}
		case 2: // UTF-8 or not
			x = []byte(badStrs[g.pick(len(badStrs))])
		default:
			x = make([]byte, g.pick(9))
			g.r.Read(x)
		}
		b = protowire.AppendBytes(b, x)
	case protowire.StartGroupType:
		b = protowire.AppendTag(b, 3, protowire.VarintType)
		b = protowire.AppendVarint(b, 1)
		endNum := num
		if g.pick(4) == 0 {
			endNum = num + 1
		}
		b = protowire.AppendTag(b, endNum, protowire.EndGroupType)
	case protowire.EndGroupType:
	default: // 6, 7
		b = append(b, 0x01)
	}
	if g.pick(5) == 0 && len(b) > 1 {
		b = b[:len(b)-1-g.pick(len(b)-1)]
	}
	return b
}

// deep is n nested levels of field `num` (length-delimited) around `inner`.
func deep(num protowire.Number, n int, inner []byte) []byte {
	b := inner
	for i := 0; i < n; i++ {
		var o []byte
		o = protowire.AppendTag(o, num, protowire.BytesType)
		o = protowire.AppendBytes(o, b)
		b = o
	}
	return b
}

// deepGroup is an unknown group numbered `num` nested n deep.
func deepGroup(num protowire.Number, n int) []byte {
	var b []byte
	for i := 0; i < n; i++ {
		b = protowire.AppendTag(b, num, protowire.StartGroupType)
	}
	for i := 0; i < n; i++ {
		b = protowire.AppendTag(b, num, protowire.EndGroupType)
	}
	return b
}

// ---- the vectors ----

type encVec struct {
	ty, value string
	out       []byte
	ok        bool
}

type decVec struct {
	ty  string
	in  []byte
	out string // "" for an error
}

func decodeVec(t *testing.T, mt protoreflect.MessageType, in []byte) decVec {
	m := mt.New().Interface()
	v := decVec{ty: string(mt.Descriptor().FullName()), in: append([]byte{}, in...)}
	if err := proto.Unmarshal(in, m); err == nil {
		v.out = leanMsg(m.ProtoReflect())
	}
	return v
}

func build(t *testing.T) string {
	g := &gen{r: rand.New(rand.NewSource(20261121))}
	var encs []encVec
	var decs []decVec
	pbgenChecked := 0
	for _, root := range roots {
		mt := root.ProtoReflect().Type()
		md := mt.Descriptor()
		ty := string(md.FullName())
		var encodings [][]byte
		for i := 0; i < encPerType; i++ {
			g.badUTF8 = i%5 == 4
			m := mt.New()
			g.fill(m, 2, i%3 == 2)
			b, err := proto.Marshal(m.Interface())
			ev := encVec{ty: ty, value: leanMsg(m), ok: err == nil}
			if err == nil {
				ev.out = b
				encodings = append(encodings, b)
			}
			encs = append(encs, ev)
			if !hasUnknown(m) {
				pb, perr, ok := pbgenMarshal(m.Interface())
				if ok {
					pbgenChecked++
					if (perr == nil) != (err == nil) || (err == nil && !bytes.Equal(pb, b)) {
						t.Errorf("%s: pbgen %x (%v), protobuf-go %x (%v)", ty, pb, perr, b, err)
					}
				}
			}
		}
		// decode: the encodings, concatenations (merges), mutations, crafted records
		for _, b := range encodings {
			decs = append(decs, decodeVec(t, mt, b))
		}
		for i := 0; i < mutPerType && len(encodings) > 0; i++ {
			a := encodings[g.pick(len(encodings))]
			c := encodings[g.pick(len(encodings))]
			var in []byte
			switch i % 3 {
			case 0:
				in = append(append([]byte{}, a...), c...)
			case 1:
				in = append([]byte{}, a...)
				if len(in) > 0 {
					in[g.pick(len(in))] ^= byte(1 << uint(g.pick(8)))
				}
			default:
				in = append([]byte{}, a...)
				if len(in) > 0 {
					in = in[:g.pick(len(in))]
				}
			}
			decs = append(decs, decodeVec(t, mt, in))
		}
		for i := 0; i < wirePerType; i++ {
			var in []byte
			for k := 0; k < 1+g.pick(3); k++ {
				in = append(in, g.wireInput(md)...)
			}
			decs = append(decs, decodeVec(t, mt, in))
		}
	}
	// the limits (written as Lean-side constructions, deepMsgBytes/deepGroupBytes below, not as
	// bytes): 10000 nested messages decode, 10001 do not (raftpb.Message's responses, 14); unknown
	// groups nested 10001 deep decode (kept as they are), 10002 do not
	msgT := (&raftpb.Message{}).ProtoReflect().Type()
	type limit struct {
		lean string
		in   []byte
	}
	limits := []limit{
		{"deepMsgBytes 9999", deep(14, 9999, nil)}, {"deepMsgBytes 10000", deep(14, 10000, nil)},
		{"deepGroupBytes 99 10001", deepGroup(99, 10001)}, {"deepGroupBytes 99 10002", deepGroup(99, 10002)},
	}
	var limitGuards []string
	for _, l := range limits {
		m := msgT.New().Interface()
		err := proto.Unmarshal(l.in, m)
		switch {
		case err != nil:
			limitGuards = append(limitGuards, fmt.Sprintf("#guard decode desc \"raftpb.Message\" (%s) == none", l.lean))
		case strings.HasPrefix(l.lean, "deepGroup") && bytes.Equal(m.ProtoReflect().GetUnknown(), l.in):
			limitGuards = append(limitGuards, fmt.Sprintf("#guard decode desc \"raftpb.Message\" (%s) == some (.msg [] (%s))", l.lean, l.lean))
		case strings.HasPrefix(l.lean, "deepMsg"):
			limitGuards = append(limitGuards, fmt.Sprintf("#guard (decode desc \"raftpb.Message\" (%s)).isSome", l.lean))
		default:
			t.Fatalf("%s: unexpected outcome", l.lean)
		}
	}
	if pbgenChecked == 0 {
		t.Errorf("no vector checked against pbgen")
	}
	t.Logf("%d encode vectors (%d checked against pbgen), %d decode vectors", len(encs), pbgenChecked, len(decs))

	d, err := pbdesc.Of(rootPaths())
	if err != nil {
		t.Fatal(err)
	}
	desc, err := leanDesc(d)
	if err != nil {
		t.Fatal(err)
	}

	var w strings.Builder
	w.WriteString(`/-
**Differential test vectors of the candidate protobuf wire semantics** (` + "`PbWire.lean`" + `, which
nothing trusts yet). Generated by ` + "`examples/pbwire`" + ` (` + "`vectors_test.go`" + `): DO NOT EDIT; rerun
` + "`cd examples && PBWIRE_UPDATE=1 GOWORK=off go test ./pbwire/`" + `. The descriptors are ` + "`models/pbdesc`" + `'s
dump of the root types' closure; each encode vector is a message built on the real generated struct
and protobuf-go v1.36.12's ` + "`proto.Marshal`" + ` of it (` + "`none`" + `: its error), checked against pbgen's codec in
Go where the type is in pbgen's subset; each decode vector is an input and ` + "`proto.Unmarshal`" + `'s message
(` + "`none`" + `: its error). The ` + "`#guard`" + `s below check ` + "`PbWire.encode`/`PbWire.decode`" + ` against every vector.
-/
module

public import Proof.google_golang_org.protobuf.proto.PbWire
-- the #guards run PbWire's code at elaboration time
public meta import Proof.google_golang_org.protobuf.proto.PbWire

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace PbWire
namespace Vectors

/-- The descriptors (` + "`models/pbdesc`" + `). -/
def desc : Desc := `)
	w.WriteString(desc)
	w.WriteString("\n")
	// the vectors in chunks (one long list literal exceeds the elaborator's recursion depth)
	const chunk = 64
	var encNames, decNames []string
	for c := 0; c*chunk < len(encs); c++ {
		name := fmt.Sprintf("encVecs%d", c)
		encNames = append(encNames, name)
		fmt.Fprintf(&w, "\n/-- Encode vectors: (type, message, `proto.Marshal`'s bytes or `none`). -/\ndef %s : List (String × Value × Option (List Byte)) := [\n", name)
		part := encs[c*chunk : min((c+1)*chunk, len(encs))]
		for i, e := range part {
			out := "none"
			if e.ok {
				out = "some " + leanHex(e.out)
			}
			sep := ","
			if i == len(part)-1 {
				sep = "]"
			}
			fmt.Fprintf(&w, "  (%q, %s, %s)%s\n", e.ty, e.value, out, sep)
		}
	}
	for c := 0; c*chunk < len(decs); c++ {
		name := fmt.Sprintf("decVecs%d", c)
		decNames = append(decNames, name)
		fmt.Fprintf(&w, "\n/-- Decode vectors: (type, input, `proto.Unmarshal`'s message or `none`). -/\ndef %s : List (String × List Byte × Option Value) := [\n", name)
		part := decs[c*chunk : min((c+1)*chunk, len(decs))]
		for i, dv := range part {
			out := "none"
			if dv.out != "" {
				out = "some " + dv.out
			}
			sep := ","
			if i == len(part)-1 {
				sep = "]"
			}
			fmt.Fprintf(&w, "  (%q, %s, %s)%s\n", dv.ty, leanHex(dv.in), out, sep)
		}
	}
	fmt.Fprintf(&w, "\ndef encVecs : List (String × Value × Option (List Byte)) :=\n  %s\n", strings.Join(encNames, " ++ "))
	fmt.Fprintf(&w, "\ndef decVecs : List (String × List Byte × Option Value) :=\n  %s\n", strings.Join(decNames, " ++ "))
	w.WriteString(`
/-- The indices of the encode vectors ` + "`encode`" + ` disagrees with. -/
def encFailures : List Nat :=
  (encVecs.zipIdx).filterMap fun ((ty, v, out), i) => if encode desc ty v == out then none else some i

/-- The indices of the decode vectors ` + "`decode`" + ` disagrees with. -/
def decFailures : List Nat :=
  (decVecs.zipIdx).filterMap fun ((ty, inp, out), i) => if decode desc ty inp == out then none else some i

#guard encFailures == []
#guard decFailures == []

/-- n nested raftpb.Message records of field responses (14), around nothing. -/
def deepMsgBytes : Nat → List Byte
  | 0 => []
  | n + 1 => let b := deepMsgBytes n; tag 14 2 ++ varint b.length ++ b

/-- An unknown group numbered num nested n deep. -/
def deepGroupBytes (num n : Nat) : List Byte :=
  (List.replicate n (tag num 3)).flatten ++ (List.replicate n (tag num 4)).flatten

` + strings.Join(limitGuards, "\n") + `

end Vectors
end PbWire
end EtcdGrove
end Perennial
`)
	return w.String()
}

// rootPaths are the roots as pbdesc names them ("import/path.GoType").
func rootPaths() []string {
	var ps []string
	for _, r := range roots {
		t := reflect.TypeOf(r).Elem()
		ps = append(ps, t.PkgPath()+"."+t.Name())
	}
	return ps
}

func TestVectors(t *testing.T) {
	got := build(t)
	if os.Getenv("PBWIRE_UPDATE") != "" {
		if err := os.WriteFile(leanPath, []byte(got), 0o644); err != nil {
			t.Fatal(err)
		}
		t.Logf("wrote %s", leanPath)
		return
	}
	cur, err := os.ReadFile(leanPath)
	if err != nil {
		t.Fatal(err)
	}
	if string(cur) != got {
		t.Fatalf("%s is not what this test writes (rerun with PBWIRE_UPDATE=1, then build it)", leanPath)
	}
}
