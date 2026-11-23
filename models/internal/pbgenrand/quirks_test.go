package pbgenrand

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

// quirksTest is the Go test TestProtobufQuirks runs in the compiled schema's package: the two
// behaviors of protobuf-go v1.36.12's required-field checks that pbgen's core refuses schemas
// for (pbgen_core.py, REFUSED), each shown on the real module.
const quirksTest = `package q

import (
	"testing"

	"google.golang.org/protobuf/proto"
)

// A oneof member other than the oneof's first, of a message type with a required field: a
// missing required field in it passes Unmarshal (its fast path consults the isInit of the
// member's own coder, which only the first member's has), and fails Marshal (whose check goes
// through the first member's coder to the set one).
func TestOneofLaterMember(t *testing.T) {
	// field 2 (member f1 of oneof u, after f0), an empty M0 (its required x missing)
	data := []byte{0x12, 0x00}
	m := &M1{}
	if err := proto.Unmarshal(data, m); err != nil {
		t.Fatalf("Unmarshal: %v (the quirk is gone: protobuf-go checks the member)", err)
	}
	if _, err := proto.Marshal(m); err == nil {
		t.Fatalf("Marshal of the decoded message did not fail")
	}
	// the first member: checked
	if err := proto.Unmarshal([]byte{0x1a, 0x00}, &M2{}); err == nil {
		t.Fatalf("Unmarshal of the first member with a required field missing did not fail")
	}
}

// A message type that reaches a required field only through a cycle (B -> A -> C, A -> B): once
// R's coder is built first (which asks needsInitCheck of A, whose traversal meets B with A in
// progress and caches false for B), B's Marshal and Unmarshal never check required fields.
func TestCycleCache(t *testing.T) {
	if _, err := proto.Marshal(&R{}); err != nil {
		t.Fatal(err)
	}
	b := &B{A: &A{C: &C{}}} // C.x (required) missing
	if _, err := proto.Marshal(b); err != nil {
		t.Fatalf("Marshal(B): %v (the quirk is gone: protobuf-go checks B)", err)
	}
	if _, err := proto.Marshal(&A{C: &C{}}); err == nil {
		t.Fatalf("Marshal(A) with C.x missing did not fail")
	}
}
`

// TestProtobufQuirks: the two behaviors of protobuf-go's required-field checks that pbgen refuses
// schemas for, shown on protobuf-go itself (a schema compiled by protoc-gen-go, a Go test against
// the real module). If this fails, protobuf-go changed: the refusals may go (and the core's doc
// and the review notes say why they are there). And pbgen refuses that schema, naming both.
func TestProtobufQuirks(t *testing.T) {
	s := newSetup(t)
	dir := t.TempDir()
	s.newModule(t, dir)
	msg := func(name string, fs ...*descriptorpb.FieldDescriptorProto) *descriptorpb.DescriptorProto {
		return &descriptorpb.DescriptorProto{Name: proto.String(name), Field: fs}
	}
	m := func(name string, num int32, typ string) *descriptorpb.FieldDescriptorProto {
		return withType(fld(name, num, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, opt), typ)
	}
	inOneof := func(f *descriptorpb.FieldDescriptorProto) *descriptorpb.FieldDescriptorProto {
		f.OneofIndex = proto.Int32(0)
		return f
	}
	m1 := msg("M1", inOneof(fld("f0", 1, i32, opt)), inOneof(m("f1", 2, ".q.M0")))
	m1.OneofDecl = []*descriptorpb.OneofDescriptorProto{{Name: proto.String("u")}}
	m2 := msg("M2", inOneof(m("g0", 3, ".q.M0")), inOneof(fld("g1", 4, i32, opt)))
	m2.OneofDecl = []*descriptorpb.OneofDescriptorProto{{Name: proto.String("v")}}
	q := refusedFile("q", "proto2",
		msg("M0", fld("x", 1, i32, req)), m1, m2,
		msg("R", m("a", 1, ".q.A")),
		msg("A", m("b", 1, ".q.B"), m("c", 2, ".q.C")),
		msg("B", m("a", 1, ".q.A")),
		msg("C", fld("x", 1, i32, req)))
	s.protocGenGo(t, dir, []*descriptorpb.FileDescriptorProto{q}, "")
	must(t, os.WriteFile(filepath.Join(dir, "q", "q_test.go"), []byte(quirksTest), 0o644))
	run(t, dir, nil, "go", "test", "-count=1", "./q")

	toml := "[protobuf]\nimports = { q = \"pbgenrand.tmp/q\" }\nroots = [\"q.M1\", \"q.M2\", \"q.R\", \"q.B\"]\n"
	tomlPath := filepath.Join(dir, "protobuf.toml")
	must(t, os.WriteFile(tomlPath, []byte(toml), 0o644))
	out, code := runCode(dir, nil, "python3", s.pbgen, tomlPath, filepath.Join(dir, "codec"), "--pkg", "codec")
	if code != 2 {
		t.Fatalf("pbgen: exit %d, not 2 (refused):\n%s", code, out)
	}
	for _, want := range []string{
		"field q.M1.f1 (number 2): a oneof member (not the first of u)",
		"message q.A: reaches required fields only through a cycle",
		"message q.B: reaches required fields only through a cycle",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("pbgen's refusal does not say %q:\n%s", want, out)
		}
	}
	for _, ok := range []string{"q.M2", "q.R:", "q.C", "q.M0"} {
		if strings.Contains(out, ok) {
			t.Errorf("pbgen refuses %s, inside the subset:\n%s", ok, out)
		}
	}
	t.Logf("protobuf-go's quirks confirmed; refused as expected:\n%s", out)
}
