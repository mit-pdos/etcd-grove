// Package pbschema checks the protobuf schemas the Lean proofs trust (per-type message models,
// stage A, [v6a] 1 and 6) against the Go descriptors of the pinned code.
//
// The Lean side (etc/PbSchemaDump.lean, run by etc/pbschema-check.py) dumps pbSchemaOf's table
// and the registered roots; this test reads the dump from $PBSCHEMA_DUMP and checks:
//
//   - every message type reachable from a root (through message-typed fields) has a Lean schema,
//     and each Lean schema is exactly the type's descriptor: for every declared field, its number
//     and the wire types protobuf-go's decoder takes for it (internal/impl: a varint kind 0, a
//     fixed64 1, a fixed32 5, bytes/string/message 2, a group 3; a repeated packable scalar both
//     its own wire type and 2, packed or not). An over-declared schema makes the decoder trust
//     (D1) false, an under-declared one the round trip (D2);
//   - D1's size bound condition (sizeBoundViolation): no reachable type has a proto2 unpacked
//     repeated int32 or enum field at any number, nor another unpacked repeated scalar numbered 16
//     or more (each would break size c <= 2|bs| on a packed input).
//
// TestSizeBoundCondition checks sizeBoundViolation itself, without the dump. The tests of
// d1post_test.go check the decoder's post D1, the round trip D2 and the encoder axioms (they need
// no dump either).
package pbschema

import (
	"bufio"
	"fmt"
	"os"
	"sort"
	"strings"
	"testing"

	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protodesc"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/reflect/protoregistry"
	"google.golang.org/protobuf/types/descriptorpb"
	"google.golang.org/protobuf/types/dynamicpb"
)

// The Go messages the Lean roots name (protobuf full names); a root missing here fails the test.
var known = map[string]protoreflect.MessageDescriptor{
	"raftpb.Entry":   (&raftpb.Entry{}).ProtoReflect().Descriptor(),
	"raftpb.Message": (&raftpb.Message{}).ProtoReflect().Descriptor(),
}

func wireTypes(f protoreflect.FieldDescriptor) []int {
	var wt int
	switch f.Kind() {
	case protoreflect.BoolKind, protoreflect.EnumKind, protoreflect.Int32Kind, protoreflect.Sint32Kind,
		protoreflect.Uint32Kind, protoreflect.Int64Kind, protoreflect.Sint64Kind, protoreflect.Uint64Kind:
		wt = 0
	case protoreflect.Fixed64Kind, protoreflect.Sfixed64Kind, protoreflect.DoubleKind:
		wt = 1
	case protoreflect.Fixed32Kind, protoreflect.Sfixed32Kind, protoreflect.FloatKind:
		wt = 5
	case protoreflect.StringKind, protoreflect.BytesKind, protoreflect.MessageKind:
		wt = 2
	case protoreflect.GroupKind:
		wt = 3
	}
	if f.IsMap() {
		return []int{2}
	}
	if f.IsList() && wt != 2 && wt != 3 {
		return []int{wt, 2}
	}
	return []int{wt}
}

// sizeBoundViolation is D1's size bound condition on one field ("" if it holds). A proto2 unpacked
// repeated scalar re-encodes each element of a packed input with its own tag: with a 1-byte tag a
// 1-byte element becomes 2 bytes (the ratio tends to 2, as ConfState's packed zeros), with a tag of
// 2 bytes or more (number >= 16) 3, past the 2x bound. An int32 or enum element is worse at any
// number: the packed 5-byte varint `ff ff ff ff 0f` decodes as int32(-1), which re-encodes
// sign-extended in 10 bytes plus its tag (protobuf-go internal/impl/codec_gen.go consumeInt32Slice,
// sizeInt32Slice; the ratio tends to 2.2).
func sizeBoundViolation(fd protoreflect.FieldDescriptor) string {
	if !fd.IsList() || fd.IsPacked() {
		return ""
	}
	switch fd.Kind() {
	case protoreflect.MessageKind, protoreflect.GroupKind, protoreflect.StringKind, protoreflect.BytesKind:
		return ""
	case protoreflect.Int32Kind, protoreflect.EnumKind:
		return fmt.Sprintf("unpacked repeated %s (number %d)", fd.Kind(), fd.Number())
	}
	if fd.Number() >= 16 {
		return fmt.Sprintf("unpacked repeated scalar numbered %d >= 16", fd.Number())
	}
	return ""
}

func render(md protoreflect.MessageDescriptor) string {
	fs := md.Fields()
	var parts []string
	nums := make([]int, 0, fs.Len())
	byNum := map[int]protoreflect.FieldDescriptor{}
	for i := 0; i < fs.Len(); i++ {
		f := fs.Get(i)
		nums = append(nums, int(f.Number()))
		byNum[int(f.Number())] = f
	}
	sort.Ints(nums)
	for _, n := range nums {
		var ws []string
		for _, w := range wireTypes(byNum[n]) {
			ws = append(ws, fmt.Sprint(w))
		}
		parts = append(parts, fmt.Sprintf("%d:%s", n, strings.Join(ws, ",")))
	}
	return strings.Join(parts, " ")
}

func normalize(fields []string) string {
	type kv struct {
		n int
		s string
	}
	var xs []kv
	for _, f := range fields {
		var n int
		fmt.Sscanf(f, "%d:", &n)
		xs = append(xs, kv{n, f})
	}
	sort.Slice(xs, func(i, j int) bool { return xs[i].n < xs[j].n })
	var out []string
	for _, x := range xs {
		out = append(out, x.s)
	}
	return strings.Join(out, " ")
}

func TestSchemas(t *testing.T) {
	path := os.Getenv("PBSCHEMA_DUMP")
	if path == "" {
		t.Skip("PBSCHEMA_DUMP not set (run etc/pbschema-check.py)")
	}
	f, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	lean := map[string]string{}
	var roots []string
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		w := strings.Fields(sc.Text())
		if len(w) == 0 {
			continue
		}
		switch w[0] {
		case "schema":
			lean[w[1]] = normalize(w[3:])
		case "root":
			roots = append(roots, w[1])
		}
	}
	if len(roots) == 0 {
		t.Fatal("no root in the dump")
	}
	seen := map[protoreflect.FullName]bool{}
	var walk func(md protoreflect.MessageDescriptor)
	walk = func(md protoreflect.MessageDescriptor) {
		if seen[md.FullName()] {
			return
		}
		seen[md.FullName()] = true
		name := string(md.FullName())
		got := render(md)
		if ls, ok := lean[name]; !ok {
			t.Errorf("%s: reachable from a root, no Lean schema (Go: %s)", name, got)
		} else if ls != got {
			t.Errorf("%s: Lean schema %q, Go descriptor %q", name, ls, got)
		} else {
			t.Logf("%s: %s (agrees)", name, got)
		}
		fs := md.Fields()
		for i := 0; i < fs.Len(); i++ {
			fd := fs.Get(i)
			if why := sizeBoundViolation(fd); why != "" {
				t.Errorf("%s.%s: %s (D1's 2x bound)", name, fd.Name(), why)
			}
			if fd.Message() != nil {
				walk(fd.Message())
			}
		}
	}
	for _, r := range roots {
		md, ok := known[r]
		if !ok {
			if d, err := protoregistry.GlobalFiles.FindDescriptorByName(protoreflect.FullName(r)); err == nil {
				if m, ok := d.(protoreflect.MessageDescriptor); ok {
					md = m
				}
			}
		}
		if md == nil {
			t.Errorf("root %s: no Go descriptor", r)
			continue
		}
		walk(md)
	}
	for name := range lean {
		if !seen[protoreflect.FullName(name)] {
			t.Errorf("%s: a Lean schema no root reaches", name)
		}
	}
}

// TestSizeBoundCondition: sizeBoundViolation on a synthetic proto2 message (each refused field breaks
// the 2x bound on a packed input under protobuf-go, each accepted one does not), and on the raftpb
// types reachable from the known roots (none refused).
func TestSizeBoundCondition(t *testing.T) {
	rep := descriptorpb.FieldDescriptorProto_LABEL_REPEATED.Enum()
	field := func(name string, num int32, typ descriptorpb.FieldDescriptorProto_Type, packed bool) *descriptorpb.FieldDescriptorProto {
		f := &descriptorpb.FieldDescriptorProto{Name: proto.String(name), Number: proto.Int32(num), Label: rep, Type: typ.Enum()}
		if packed {
			f.Options = &descriptorpb.FieldOptions{Packed: proto.Bool(true)}
		}
		return f
	}
	T := descriptorpb.FieldDescriptorProto_TYPE_INT32
	U := descriptorpb.FieldDescriptorProto_TYPE_UINT64
	S := descriptorpb.FieldDescriptorProto_TYPE_SINT32
	E := descriptorpb.FieldDescriptorProto_TYPE_ENUM
	en := field("e", 5, E, false)
	en.TypeName = proto.String(".sbc.En")
	fdp := &descriptorpb.FileDescriptorProto{
		Name: proto.String("sbc.proto"), Package: proto.String("sbc"), Syntax: proto.String("proto2"),
		EnumType: []*descriptorpb.EnumDescriptorProto{{Name: proto.String("En"),
			Value: []*descriptorpb.EnumValueDescriptorProto{{Name: proto.String("Z"), Number: proto.Int32(0)},
				{Name: proto.String("NEG"), Number: proto.Int32(-1)}}}},
		MessageType: []*descriptorpb.DescriptorProto{{Name: proto.String("M"), Field: []*descriptorpb.FieldDescriptorProto{
			field("i32", 1, T, false), field("u64", 2, U, false), field("u64hi", 16, U, false),
			field("i32packed", 3, T, true), field("s32", 4, S, false), en}}},
	}
	fd, err := protodesc.NewFile(fdp, nil)
	if err != nil {
		t.Fatal(err)
	}
	md := fd.Messages().ByName("M")
	want := map[string]bool{"i32": true, "u64": false, "u64hi": true, "i32packed": false, "s32": false, "e": true}
	for name, refused := range want {
		f := md.Fields().ByName(protoreflect.Name(name))
		if got := sizeBoundViolation(f) != ""; got != refused {
			t.Errorf("sizeBoundViolation(M.%s) refuses %v, want %v", name, got, refused)
		}
		// the worst packed input for the field: k elements, -1 as a 5-byte varint (int32, enum),
		// otherwise 0 (1 byte)
		const k = 1000
		var body []byte
		for i := 0; i < k; i++ {
			if f.Kind() == protoreflect.Int32Kind || f.Kind() == protoreflect.EnumKind {
				body = append(body, 0xff, 0xff, 0xff, 0xff, 0x0f)
			} else {
				body = append(body, 0)
			}
		}
		bs := protowire.AppendBytes(protowire.AppendTag(nil, f.Number(), protowire.BytesType), body)
		m := dynamicpb.NewMessage(md)
		if err := proto.Unmarshal(bs, m); err != nil {
			t.Fatalf("M.%s: %v", name, err)
		}
		sz := proto.Size(m)
		if broken := sz > 2*len(bs); broken != refused {
			t.Errorf("M.%s: packed input %d bytes, proto.Size %d: bound broken %v, refused %v", name, len(bs), sz, broken, refused)
		} else {
			t.Logf("M.%s: packed input %d bytes, proto.Size %d (ratio %.3f), refused %v", name, len(bs), sz, float64(sz)/float64(len(bs)), refused)
		}
	}
	seen := map[protoreflect.FullName]bool{}
	var walk func(md protoreflect.MessageDescriptor)
	walk = func(md protoreflect.MessageDescriptor) {
		if seen[md.FullName()] {
			return
		}
		seen[md.FullName()] = true
		for i := 0; i < md.Fields().Len(); i++ {
			f := md.Fields().Get(i)
			if why := sizeBoundViolation(f); why != "" {
				t.Errorf("%s.%s: %s", md.FullName(), f.Name(), why)
			}
			if f.Message() != nil {
				walk(f.Message())
			}
		}
	}
	for _, md := range known {
		walk(md)
	}
	t.Logf("%d raftpb types reachable from the known roots: none refused", len(seen))
}
