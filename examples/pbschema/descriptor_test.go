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
//   - D1's size bound condition: no reachable type has a proto2 unpacked repeated scalar field
//     numbered 16 or more (a 2-byte tag re-encoded packed would break size c <= 2|bs|).
package pbschema

import (
	"bufio"
	"fmt"
	"os"
	"sort"
	"strings"
	"testing"

	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/reflect/protoregistry"
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
			if fd.IsList() && !fd.IsPacked() && fd.Number() >= 16 && fd.Kind() != protoreflect.MessageKind &&
				fd.Kind() != protoreflect.StringKind && fd.Kind() != protoreflect.BytesKind &&
				fd.Kind() != protoreflect.GroupKind {
				t.Errorf("%s.%s: unpacked repeated scalar numbered %d >= 16 (D1's 2x bound)", name, fd.Name(), fd.Number())
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
