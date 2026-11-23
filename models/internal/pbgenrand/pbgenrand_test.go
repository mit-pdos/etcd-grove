// Package pbgenrand is the differential test of the protobuf codec generator itself
// (models/protobuf/pbgen.py, whose core pbgen_core.py is the trusted artifact): random schemas
// within its subset, each compiled to real Go code by the real protoc-gen-go (v1.36.12, built from the
// module cache; no protoc: the test builds the FileDescriptorProtos itself and hands them to the
// plugin as a CodeGeneratorRequest), the generator run on them (its schema dump included), and
// the generated codec compared with real protobuf-go by the regression test the generator
// writes beside it (pb_gen_test.go: Marshal of random values byte for byte and nil-or-not;
// Unmarshal of real encodings, of their mutations and of every field number with every wire type,
// error-or-not and the value; the recursion limits; the panics). And schemas outside the subset,
// one unsupported construct each, which the generator must refuse, naming message and field.
//
// Environment: PBGEN_RAND_SCHEMAS (schemas per run, default 24), PBGEN_RAND_SEED (default 1),
// PBGEN_RAND_BATCH (schemas per compiled Go module, default 12), PBGEN_TEST_SCALE (the count of
// random values per type in the generated tests, default 0.2 here). By hand, e.g.:
//
//	PBGEN_RAND_SCHEMAS=200 PBGEN_RAND_SEED=$RANDOM PBGEN_TEST_SCALE=1 go test -count=1 -v -timeout 2h ./internal/pbgenrand
//
// The test needs python3 and the generator (protobuf/pbgen.py in this module); without them it
// is skipped.
package pbgenrand

import (
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"google.golang.org/protobuf/encoding/prototext"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protodesc"
	"google.golang.org/protobuf/types/descriptorpb"
	"google.golang.org/protobuf/types/pluginpb"
)

func envInt(name string, def int64) int64 {
	if v, err := strconv.ParseInt(os.Getenv(name), 10, 64); err == nil {
		return v
	}
	return def
}

// setup: the repository's pbgen.py, the models module root, and a protoc-gen-go binary.
type setup struct {
	pbgen, modRoot, plugin string
}

func newSetup(t *testing.T) setup {
	t.Helper()
	wd, _ := os.Getwd()
	modRoot := filepath.Clean(filepath.Join(wd, "..", ".."))
	gen := filepath.Join(modRoot, "protobuf")
	pbgen := filepath.Join(gen, "pbgen.py")
	// read the generator's files here, so that go test's cache sees them change
	for _, f := range []string{"pbgen.py", "pbgen_core.py", "pbgen_testgen.py"} {
		if _, err := os.ReadFile(filepath.Join(gen, f)); err != nil {
			t.Skipf("no %s (the generator): %v", f, err)
		}
	}
	if _, err := exec.LookPath("python3"); err != nil {
		t.Skip("no python3")
	}
	plugin := filepath.Join(t.TempDir(), "protoc-gen-go")
	run(t, modRoot, nil, "go", "build", "-o", plugin, "google.golang.org/protobuf/cmd/protoc-gen-go")
	return setup{pbgen, modRoot, plugin}
}

func goEnv(extra ...string) []string {
	return append(os.Environ(), append([]string{"GOWORK=off", "GOPROXY=off", "GOFLAGS=-mod=mod"}, extra...)...)
}

func run(t *testing.T, dir string, env []string, name string, args ...string) string {
	t.Helper()
	out, code := runCode(dir, env, name, args...)
	if code != 0 {
		t.Fatalf("%s %s (in %s): exit %d\n%s", name, strings.Join(args, " "), dir, code, out)
	}
	return out
}

func runCode(dir string, env []string, name string, args ...string) (string, int) {
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	if env == nil {
		env = goEnv()
	}
	cmd.Env = env
	var buf bytes.Buffer
	cmd.Stdout, cmd.Stderr = &buf, &buf
	err := cmd.Run()
	if ee, ok := err.(*exec.ExitError); ok {
		return buf.String(), ee.ExitCode()
	}
	if err != nil {
		return buf.String() + err.Error(), -1
	}
	return buf.String(), 0
}

// newModule writes a Go module pbgenrand.tmp into dir that can import models.lab.
func (s setup) newModule(t *testing.T, dir string) {
	t.Helper()
	gomod := fmt.Sprintf("module pbgenrand.tmp\n\ngo 1.27\n\nrequire (\n\tgoogle.golang.org/protobuf v1.36.12\n"+
		"\tmodels.lab v0.0.0-00010101000000-000000000000\n)\n\nreplace models.lab => %s\n", s.modRoot)
	must(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(gomod), 0o644))
	sum, err := os.ReadFile(filepath.Join(s.modRoot, "go.sum"))
	must(t, err)
	must(t, os.WriteFile(filepath.Join(dir, "go.sum"), sum, 0o644))
}

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

// protocGenGo runs the real protoc-gen-go on files (dependencies first; all generated) and writes
// the .pb.go files into dir (paths=source_relative).
func (s setup) protocGenGo(t *testing.T, dir string, files []*descriptorpb.FileDescriptorProto, param string) {
	t.Helper()
	fset := &descriptorpb.FileDescriptorSet{File: files}
	if _, err := protodesc.NewFiles(fset); err != nil {
		t.Fatalf("an invalid schema (the test's bug): %v\n%s", err, prototext.Format(fset))
	}
	req := &pluginpb.CodeGeneratorRequest{ProtoFile: files, Parameter: proto.String("paths=source_relative" + param)}
	for _, f := range files {
		req.FileToGenerate = append(req.FileToGenerate, f.GetName())
	}
	in, err := proto.Marshal(req)
	must(t, err)
	cmd := exec.Command(s.plugin)
	cmd.Stdin = bytes.NewReader(in)
	var out, errb bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &errb
	if err := cmd.Run(); err != nil {
		t.Fatalf("protoc-gen-go: %v\n%s", err, errb.String())
	}
	resp := &pluginpb.CodeGeneratorResponse{}
	must(t, proto.Unmarshal(out.Bytes(), resp))
	if resp.Error != nil {
		t.Fatalf("protoc-gen-go: %s\n%s", resp.GetError(), prototext.Format(fset))
	}
	for _, f := range resp.File {
		p := filepath.Join(dir, f.GetName())
		must(t, os.MkdirAll(filepath.Dir(p), 0o755))
		must(t, os.WriteFile(p, []byte(f.GetContent()), 0o644))
	}
}

// ---------------------------------------------------------------------------------------------
// Random schemas of the subset

var scalarTypes = []descriptorpb.FieldDescriptorProto_Type{
	descriptorpb.FieldDescriptorProto_TYPE_INT32, descriptorpb.FieldDescriptorProto_TYPE_INT64,
	descriptorpb.FieldDescriptorProto_TYPE_UINT32, descriptorpb.FieldDescriptorProto_TYPE_UINT64,
	descriptorpb.FieldDescriptorProto_TYPE_SINT32, descriptorpb.FieldDescriptorProto_TYPE_SINT64,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32, descriptorpb.FieldDescriptorProto_TYPE_FIXED64,
	descriptorpb.FieldDescriptorProto_TYPE_SFIXED32, descriptorpb.FieldDescriptorProto_TYPE_SFIXED64,
	descriptorpb.FieldDescriptorProto_TYPE_BOOL, descriptorpb.FieldDescriptorProto_TYPE_STRING,
	descriptorpb.FieldDescriptorProto_TYPE_BYTES,
}

// fieldNums: field numbers the schemas favor (one- and two-byte tags at their edges, the
// largest, around the reserved range), besides random ones.
var fieldNums = []int32{1, 2, 3, 4, 5, 15, 16, 17, 127, 128, 2047, 2048, 2049, 18999, 20000, 262143,
	262144, 536870910, 536870911}

// specialNames: field names whose Go names protoc-gen-go must change (methods of the message).
var specialNames = []string{"reset", "string", "descriptor", "proto_message", "get_x"}

// goPkgNames: Go package names a schema's package may take besides its own: a name shared by
// several schemas, and names the codec uses for itself (the generator must alias them).
var goPkgNames = []string{"pb", "pb", "m", "b", "pbcodec", "proto", "bytes", "e"}

type msgRef struct {
	full   string // ".pkg.M0.N"
	goName string // "M0_N"
}

type schemaGen struct {
	r *rand.Rand
	// closed: the enums generated so far that are closed (of proto2 files)
	closed map[string]bool
}

// defaultFor: a random default value (the descriptor's text form) for a singular field of
// scalar type typ, or of enum e (one of its value names).
func (g schemaGen) defaultFor(typ descriptorpb.FieldDescriptorProto_Type, e *descriptorpb.EnumDescriptorProto) string {
	r := g.r
	switch typ {
	case descriptorpb.FieldDescriptorProto_TYPE_BOOL:
		return []string{"true", "false"}[r.Intn(2)]
	case descriptorpb.FieldDescriptorProto_TYPE_STRING:
		return []string{"", "x", "d\u00e9faut"}[r.Intn(3)]
	case descriptorpb.FieldDescriptorProto_TYPE_BYTES:
		return []string{"", "ab", "\\001\\377"}[r.Intn(3)]
	case descriptorpb.FieldDescriptorProto_TYPE_ENUM:
		return e.GetValue()[r.Intn(len(e.GetValue()))].GetName()
	case descriptorpb.FieldDescriptorProto_TYPE_UINT32, descriptorpb.FieldDescriptorProto_TYPE_FIXED32:
		return []string{"0", "7", "4294967295"}[r.Intn(3)]
	case descriptorpb.FieldDescriptorProto_TYPE_UINT64, descriptorpb.FieldDescriptorProto_TYPE_FIXED64:
		return []string{"0", "7", "18446744073709551615"}[r.Intn(3)]
	case descriptorpb.FieldDescriptorProto_TYPE_INT32, descriptorpb.FieldDescriptorProto_TYPE_SINT32,
		descriptorpb.FieldDescriptorProto_TYPE_SFIXED32:
		return []string{"0", "-7", "2147483647", "-2147483648"}[r.Intn(4)]
	}
	return []string{"0", "-7", "9223372036854775807", "-9223372036854775808"}[r.Intn(4)]
}

// file is a random proto2 or proto3 file: messages (some nested), enums (some nested), fields
// of every kind referring to its own types and to those of deps; in proto2 files optional
// (explicit presence), required and repeated fields (unpacked, or packed), defaults and closed
// enums; in proto3 files implicit presence, proto3 `optional` and repeated fields (packed, or
// unpacked); oneofs in both (scalars, enums, messages).
func (g schemaGen) file(name, pkg, goPath, goPkg, syntax string, deps []*descriptorpb.FileDescriptorProto,
	depMsgs []msgRef, depEnums []string) (*descriptorpb.FileDescriptorProto, []msgRef, []string) {
	r := g.r
	proto2 := syntax == "proto2"
	fd := &descriptorpb.FileDescriptorProto{
		Name:    proto.String(name),
		Package: proto.String(pkg),
		Syntax:  proto.String(syntax),
		Options: &descriptorpb.FileOptions{GoPackage: proto.String(goPath + ";" + goPkg)},
	}
	if proto2 && r.Intn(4) == 0 {
		fd.Syntax = nil // proto2 by default
	}
	for _, d := range deps {
		fd.Dependency = append(fd.Dependency, d.GetName())
	}
	var msgs []msgRef
	var enums []string
	enumDesc := map[string]*descriptorpb.EnumDescriptorProto{}
	newEnum := func(name, full string) *descriptorpb.EnumDescriptorProto {
		ed := &descriptorpb.EnumDescriptorProto{Name: proto.String(name)}
		prefix := strings.ReplaceAll(strings.TrimPrefix(full, "."), ".", "_")
		vals := []int32{1, 2, -1, 7, 2147483647, -2147483648, 100}
		r.Shuffle(len(vals), func(i, j int) { vals[i], vals[j] = vals[j], vals[i] })
		if !proto2 || r.Intn(2) == 0 { // open enums start at 0; closed ones need not
			ed.Value = append(ed.Value, &descriptorpb.EnumValueDescriptorProto{
				Name: proto.String(prefix + "_ZERO"), Number: proto.Int32(0)})
		}
		for i := 0; i < r.Intn(4) || len(ed.Value) == 0; i++ {
			ed.Value = append(ed.Value, &descriptorpb.EnumValueDescriptorProto{
				Name: proto.String(fmt.Sprintf("%s_V%d", prefix, i)), Number: proto.Int32(vals[i])})
		}
		enums = append(enums, full)
		g.closed[full] = proto2
		enumDesc[full] = ed
		return ed
	}
	nm := 1 + r.Intn(4)
	var all []*descriptorpb.DescriptorProto
	for i := 0; i < nm; i++ {
		mn := fmt.Sprintf("M%d", i)
		md := &descriptorpb.DescriptorProto{Name: proto.String(mn)}
		fd.MessageType = append(fd.MessageType, md)
		all = append(all, md)
		msgs = append(msgs, msgRef{"." + pkg + "." + mn, mn})
		if r.Intn(3) == 0 {
			nd := &descriptorpb.DescriptorProto{Name: proto.String("N")}
			md.NestedType = append(md.NestedType, nd)
			all = append(all, nd)
			msgs = append(msgs, msgRef{"." + pkg + "." + mn + ".N", mn + "_N"})
		}
		if r.Intn(4) == 0 {
			md.EnumType = append(md.EnumType, newEnum("NE", "."+pkg+"."+mn+".NE"))
		}
	}
	for i := 0; i < r.Intn(3); i++ {
		en := fmt.Sprintf("E%d", i)
		fd.EnumType = append(fd.EnumType, newEnum(en, "."+pkg+"."+en))
	}
	msgPool := append(append([]msgRef{}, msgs...), depMsgs...)
	var enumPool []string // a proto3 field may only use open enums
	for _, e := range append(append([]string{}, enums...), depEnums...) {
		if proto2 || !g.closed[e] {
			enumPool = append(enumPool, e)
		}
	}
	for _, md := range all {
		nf := r.Intn(11)
		if r.Intn(7) == 0 {
			nf = 0 // an empty message
		}
		// the fields: nf plain ones, then the members of 0..2 oneofs (consecutive, as protodesc
		// requires), then proto3 `optional` ones (their synthetic oneofs after the real ones)
		var groups []int // the oneofs' sizes
		for k := r.Intn(3); k > 0; k-- {
			if r.Intn(2) == 0 {
				groups = append(groups, 1+r.Intn(4))
			}
		}
		nopt := 0
		if !proto2 && r.Intn(2) == 0 {
			nopt = 1 + r.Intn(3)
		}
		total := nf + nopt
		for _, k := range groups {
			total += k
		}
		used := map[int32]bool{}
		usedName := map[string]bool{}
		for j := 0; j < total; j++ {
			var num int32
			for num == 0 || used[num] {
				if r.Intn(2) == 0 {
					num = fieldNums[r.Intn(len(fieldNums))]
				} else {
					num = 1 + r.Int31n(536870911)
					if num >= 19000 && num <= 19999 {
						num = 0
					}
				}
			}
			used[num] = true
			// which part: plain (j < nf), oneof g, or proto3 optional
			oneof := int32(-1)
			acc := nf
			for gi, k := range groups {
				if j >= acc && j < acc+k {
					oneof = int32(gi)
				}
				acc += k
			}
			p3opt := j >= acc
			name := fmt.Sprintf("f%d", j)
			if s := specialNames[r.Intn(len(specialNames))]; r.Intn(8) == 0 && !usedName[s] {
				name = s
			}
			if oneof >= 0 && r.Intn(6) == 0 && !usedName["n"] {
				name = "n" // its wrapper M_N collides with a nested message N (protoc-gen-go renames it)
			}
			usedName[name] = true
			f := &descriptorpb.FieldDescriptorProto{
				Name:     proto.String(name),
				Number:   proto.Int32(num),
				Label:    descriptorpb.FieldDescriptorProto_LABEL_OPTIONAL.Enum(),
				JsonName: proto.String(jsonName(name)),
			}
			plain := oneof < 0 && !p3opt
			if plain && r.Intn(3) == 0 {
				f.Label = descriptorpb.FieldDescriptorProto_LABEL_REPEATED.Enum()
			} else if plain && proto2 && r.Intn(10) == 0 {
				f.Label = descriptorpb.FieldDescriptorProto_LABEL_REQUIRED.Enum()
			}
			switch k := r.Intn(10); {
			case k < 6 || (k < 8 && len(enumPool) == 0):
				f.Type = scalarTypes[r.Intn(len(scalarTypes))].Enum()
			case k < 8:
				f.Type = descriptorpb.FieldDescriptorProto_TYPE_ENUM.Enum()
				f.TypeName = proto.String(enumPool[r.Intn(len(enumPool))])
			default:
				f.Type = descriptorpb.FieldDescriptorProto_TYPE_MESSAGE.Enum()
				f.TypeName = proto.String(msgPool[r.Intn(len(msgPool))].full)
			}
			rep := f.GetLabel() == descriptorpb.FieldDescriptorProto_LABEL_REPEATED
			numeric := f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_STRING &&
				f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_BYTES &&
				f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_MESSAGE
			if rep && numeric && r.Intn(3) == 0 {
				f.Options = &descriptorpb.FieldOptions{Packed: proto.Bool(proto2)} // the other way
			}
			if proto2 && !rep && oneof < 0 && f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_MESSAGE && r.Intn(4) == 0 {
				var e *descriptorpb.EnumDescriptorProto
				if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_ENUM {
					e = enumDesc[f.GetTypeName()]
				}
				if f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_ENUM || e != nil {
					f.DefaultValue = proto.String(g.defaultFor(f.GetType(), e))
				}
			}
			if oneof >= 0 {
				f.OneofIndex = proto.Int32(oneof)
			}
			if p3opt {
				f.Proto3Optional = proto.Bool(true)
				f.OneofIndex = proto.Int32(int32(len(md.OneofDecl)))
				md.OneofDecl = append(md.OneofDecl, &descriptorpb.OneofDescriptorProto{Name: proto.String("_" + name)})
			} else if oneof >= 0 && int(oneof) >= len(md.OneofDecl) {
				md.OneofDecl = append(md.OneofDecl, &descriptorpb.OneofDescriptorProto{
					Name: proto.String(fmt.Sprintf("u%d", oneof))})
			}
			md.Field = append(md.Field, f)
		}
	}
	return fd, msgs, enums
}

// avoidQuirks changes a random schema (its files) where pbgen refuses a schema because
// protobuf-go's own required-field checks differ from what the descriptors say (pbgen_core.py,
// the refusals for required fields): a message field to an int32 field, until no message type
// that needs required checks is a oneof member other than the oneof's first declared one, and
// none needs them only through a cycle of two or more message types. (TestRefusals has one of
// each.)
func avoidQuirks(files []*descriptorpb.FileDescriptorProto) {
	msgs := map[string]*descriptorpb.DescriptorProto{}
	var walk func(prefix string, ms []*descriptorpb.DescriptorProto)
	walk = func(prefix string, ms []*descriptorpb.DescriptorProto) {
		for _, m := range ms {
			full := prefix + "." + m.GetName()
			msgs[full] = m
			walk(full, m.NestedType)
		}
	}
	for _, f := range files {
		walk("."+f.GetPackage(), f.MessageType)
	}
	isMsg := func(f *descriptorpb.FieldDescriptorProto) bool {
		return f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE && msgs[f.GetTypeName()] != nil
	}
	direct := func(m *descriptorpb.DescriptorProto) bool {
		for _, f := range m.Field {
			if f.GetLabel() == descriptorpb.FieldDescriptorProto_LABEL_REQUIRED {
				return true
			}
		}
		return false
	}
	reaches := func(from, to string) bool {
		seen := map[string]bool{}
		todo := []string{from}
		for len(todo) > 0 {
			t := todo[len(todo)-1]
			todo = todo[:len(todo)-1]
			for _, f := range msgs[t].Field {
				if isMsg(f) && !seen[f.GetTypeName()] {
					if f.GetTypeName() == to {
						return true
					}
					seen[f.GetTypeName()] = true
					todo = append(todo, f.GetTypeName())
				}
			}
		}
		return false
	}
	toInt32 := func(f *descriptorpb.FieldDescriptorProto) {
		f.Type = descriptorpb.FieldDescriptorProto_TYPE_INT32.Enum()
		f.TypeName = nil
	}
	for changed := true; changed; {
		changed = false
		needs := map[string]bool{}
		for grow := true; grow; {
			grow = false
			for full, m := range msgs {
				if needs[full] {
					continue
				}
				n := direct(m)
				for _, f := range m.Field {
					n = n || (isMsg(f) && needs[f.GetTypeName()])
				}
				if n {
					needs[full], grow = true, true
				}
			}
		}
		for full, m := range msgs {
			first := map[int32]bool{}
			for _, f := range m.Field {
				if f.OneofIndex == nil || f.GetProto3Optional() {
					continue
				}
				if !first[f.GetOneofIndex()] {
					first[f.GetOneofIndex()] = true
				} else if isMsg(f) && needs[f.GetTypeName()] {
					toInt32(f)
					changed = true
				}
			}
			if needs[full] && !direct(m) {
				for _, f := range m.Field {
					if isMsg(f) && f.GetTypeName() != full && reaches(f.GetTypeName(), full) {
						toInt32(f)
						changed = true
					}
				}
			}
		}
	}
}

// jsonName is protoc's default json_name (lowerCamelCase).
func jsonName(s string) string {
	var b strings.Builder
	up := false
	for _, c := range s {
		if c == '_' {
			up = true
			continue
		}
		if up && c >= 'a' && c <= 'z' {
			c -= 'a' - 'A'
		}
		up = false
		b.WriteRune(c)
	}
	return b.String()
}

var logRe = regexp.MustCompile(`(\d+) encodings, (\d+) errors|(\d+) decoded, (\d+) errors`)

// TestRandomSchemas: random schemas of the subset, the generated codecs against real protobuf-go.
func TestRandomSchemas(t *testing.T) {
	s := newSetup(t)
	n := envInt("PBGEN_RAND_SCHEMAS", 24)
	seed := envInt("PBGEN_RAND_SEED", 1)
	batch := envInt("PBGEN_RAND_BATCH", 12)
	scale := os.Getenv("PBGEN_TEST_SCALE")
	if scale == "" {
		scale = "0.2"
	}
	r := rand.New(rand.NewSource(seed))
	g := schemaGen{r, map[string]bool{}}
	var types, fields, encs, encErrs, decs, decErrs int
	var cov coverage
	for b0 := int64(0); b0 < n; b0 += batch {
		dir := t.TempDir()
		s.newModule(t, dir)
		var files []*descriptorpb.FileDescriptorProto
		var roots []string
		imports := map[string]string{}
		for i := b0; i < n && i < b0+batch; i++ {
			// a schema: file a, and sometimes file b over a
			pa := fmt.Sprintf("s%da", i)
			gpa := pa
			if r.Intn(4) == 0 {
				gpa = goPkgNames[r.Intn(len(goPkgNames))]
			}
			syn := []string{"proto3", "proto2"}[r.Intn(2)]
			fa, ma, ea := g.file(pa+"/"+pa+".proto", pa, "pbgenrand.tmp/"+pa, gpa, syn, nil, nil, nil)
			files = append(files, fa)
			ms := []msgRef{}
			for _, m := range ma {
				ms = append(ms, m)
			}
			paths := map[string]string{}
			for _, m := range ma {
				paths[m.full] = pa
			}
			if r.Intn(2) == 0 {
				pb := fmt.Sprintf("s%db", i)
				gpb := pb
				if r.Intn(4) == 0 {
					gpb = goPkgNames[r.Intn(len(goPkgNames))]
				}
				fb, mb, _ := g.file(pb+"/"+pb+".proto", pb, "pbgenrand.tmp/"+pb, gpb,
					[]string{"proto3", "proto2"}[r.Intn(2)], []*descriptorpb.FileDescriptorProto{fa}, ma, ea)
				files = append(files, fb)
				for _, m := range mb {
					ms = append(ms, m)
					paths[m.full] = pb
				}
			}
			if len(files) > 0 && files[len(files)-1] != fa {
				avoidQuirks(files[len(files)-2:])
			} else {
				avoidQuirks(files[len(files)-1:])
			}
			// roots: one or more messages of the schema; their packages named in imports
			r.Shuffle(len(ms), func(i, j int) { ms[i], ms[j] = ms[j], ms[i] })
			for _, m := range ms[:1+r.Intn(len(ms))] {
				dirName := paths[m.full]
				alias := "a" + dirName
				imports[alias] = "pbgenrand.tmp/" + dirName
				roots = append(roots, alias+"."+m.goName)
			}
		}
		cov.add(files)
		s.protocGenGo(t, dir, files, "")
		var toml strings.Builder
		toml.WriteString("[protobuf]\nimports = { ")
		first := true
		for a, p := range imports {
			if !first {
				toml.WriteString(", ")
			}
			first = false
			fmt.Fprintf(&toml, "%s = %q", a, p)
		}
		toml.WriteString(" }\nroots = [")
		for i, rt := range roots {
			if i > 0 {
				toml.WriteString(", ")
			}
			fmt.Fprintf(&toml, "%q", rt)
		}
		toml.WriteString("]\n")
		tomlPath := filepath.Join(dir, "protobuf.toml")
		must(t, os.WriteFile(tomlPath, []byte(toml.String()), 0o644))
		schema := prototext.Format(&descriptorpb.FileDescriptorSet{File: files})
		out, code := runCode(dir, nil, "python3", s.pbgen, tomlPath, filepath.Join(dir, "codec"), "--pkg", "codec")
		if code != 0 {
			t.Fatalf("seed %d, schemas %d..: pbgen refused or failed (exit %d) a schema of the subset:\n%s\n"+
				"toml:\n%s\nschema:\n%s", seed, b0, code, out, toml.String(), schema)
		}
		if m := regexp.MustCompile(`(\d+) message types, (\d+) fields`).FindStringSubmatch(out); m != nil {
			a, _ := strconv.Atoi(m[1])
			b, _ := strconv.Atoi(m[2])
			types += a
			fields += b
		}
		out, code = runCode(dir, goEnv("PBGEN_TEST_SCALE="+scale), "go", "test", "-count=1", "-v", "-timeout", "60m", "./codec")
		if code != 0 {
			t.Fatalf("seed %d, schemas %d..: the generated codec differs from protobuf-go:\n%s\ntoml:\n%s\nschema:\n%s",
				seed, b0, tail(out, 60), toml.String(), schema)
		}
		for _, m := range logRe.FindAllStringSubmatch(out, -1) {
			if m[1] != "" {
				a, _ := strconv.Atoi(m[1])
				b, _ := strconv.Atoi(m[2])
				encs, encErrs = encs+a, encErrs+b
			} else {
				a, _ := strconv.Atoi(m[3])
				b, _ := strconv.Atoi(m[4])
				decs, decErrs = decs+a, decErrs+b
			}
		}
	}
	t.Logf("seed %d: %d schemas, %d message types, %d fields; Marshal: %d encodings equal, %d errors "+
		"agreed; mutated encodings: %d decodes equal, %d errors agreed (plus the fixed field, depth "+
		"and panic tests per type)", seed, n, types, fields, encs, encErrs, decs, decErrs)
	t.Logf("the schemas' constructs (all declared, reached by the roots or not): %s", cov)
}

// coverage counts the constructs of the random schemas.
type coverage struct {
	proto2, proto3, explicit, p3optional, required, defaults, oneofs, oneofFields, unpacked, packed,
	closedEnums int
}

func (c *coverage) add(files []*descriptorpb.FileDescriptorProto) {
	var walk func(ms []*descriptorpb.DescriptorProto, proto2 bool)
	walk = func(ms []*descriptorpb.DescriptorProto, proto2 bool) {
		for _, m := range ms {
			for _, o := range m.OneofDecl {
				if !strings.HasPrefix(o.GetName(), "_") {
					c.oneofs++
				}
			}
			for _, f := range m.Field {
				rep := f.GetLabel() == descriptorpb.FieldDescriptorProto_LABEL_REPEATED
				msg := f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE
				switch {
				case f.GetProto3Optional():
					c.p3optional++
				case f.OneofIndex != nil:
					c.oneofFields++
				case proto2 && !rep && !msg:
					c.explicit++
				}
				if f.GetLabel() == descriptorpb.FieldDescriptorProto_LABEL_REQUIRED {
					c.required++
				}
				if f.DefaultValue != nil {
					c.defaults++
				}
				if rep && !msg && f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_STRING &&
					f.GetType() != descriptorpb.FieldDescriptorProto_TYPE_BYTES {
					if (proto2 && !f.GetOptions().GetPacked()) || (!proto2 && f.GetOptions() != nil && !f.GetOptions().GetPacked()) {
						c.unpacked++
					} else {
						c.packed++
					}
				}
			}
			walk(m.NestedType, proto2)
		}
	}
	for _, f := range files {
		proto2 := f.GetSyntax() != "proto3"
		if proto2 {
			c.proto2++
			c.closedEnums += len(f.EnumType)
			for _, m := range f.MessageType {
				c.closedEnums += len(m.EnumType)
			}
		} else {
			c.proto3++
		}
		walk(f.MessageType, proto2)
	}
}

func (c coverage) String() string {
	return fmt.Sprintf("%d proto2 and %d proto3 files; %d proto2 optional or required non-message fields "+
		"(%d required), %d proto3 optional, %d defaults, %d oneofs (%d members), %d unpacked and %d packed "+
		"repeated scalars, %d closed enums", c.proto2, c.proto3, c.explicit, c.required, c.p3optional,
		c.defaults, c.oneofs, c.oneofFields, c.unpacked, c.packed, c.closedEnums)
}

func tail(s string, n int) string {
	l := strings.Split(s, "\n")
	if len(l) > n {
		l = l[len(l)-n:]
	}
	return strings.Join(l, "\n")
}

// ---------------------------------------------------------------------------------------------
// Schemas outside the subset

func fld(name string, num int32, typ descriptorpb.FieldDescriptorProto_Type, label descriptorpb.FieldDescriptorProto_Label) *descriptorpb.FieldDescriptorProto {
	return &descriptorpb.FieldDescriptorProto{Name: proto.String(name), Number: proto.Int32(num), Type: typ.Enum(),
		Label: label.Enum(), JsonName: proto.String(jsonName(name))}
}

const (
	opt = descriptorpb.FieldDescriptorProto_LABEL_OPTIONAL
	rep = descriptorpb.FieldDescriptorProto_LABEL_REPEATED
	req = descriptorpb.FieldDescriptorProto_LABEL_REQUIRED
	i32 = descriptorpb.FieldDescriptorProto_TYPE_INT32
)

func withType(f *descriptorpb.FieldDescriptorProto, name string) *descriptorpb.FieldDescriptorProto {
	f.TypeName = proto.String(name)
	return f
}

func refusedFile(name, syntax string, msgs ...*descriptorpb.DescriptorProto) *descriptorpb.FileDescriptorProto {
	f := &descriptorpb.FileDescriptorProto{
		Name: proto.String(name + "/" + name + ".proto"), Package: proto.String(name),
		Options:     &descriptorpb.FileOptions{GoPackage: proto.String("pbgenrand.tmp/" + name + ";" + name)},
		MessageType: msgs,
	}
	if syntax == "editions" {
		f.Syntax = proto.String("editions")
		f.Edition = descriptorpb.Edition_EDITION_2023.Enum()
	} else {
		f.Syntax = proto.String(syntax)
	}
	return f
}

// TestRefusals: one unsupported construct per message; pbgen must refuse the schema (exit 2,
// nothing written), naming each message and field, and say nothing of the constructs inside
// the subset beside them.
func TestRefusals(t *testing.T) {
	s := newSetup(t)
	dir := t.TempDir()
	s.newModule(t, dir)
	p2 := refusedFile("p2", "proto2",
		&descriptorpb.DescriptorProto{Name: proto.String("P2"),
			Field: []*descriptorpb.FieldDescriptorProto{
				fld("x", 1, i32, opt), fld("r", 3, i32, req),
				func() *descriptorpb.FieldDescriptorProto {
					f := fld("d", 4, i32, opt)
					f.DefaultValue = proto.String("5")
					return f
				}(),
				withType(fld("c", 5, descriptorpb.FieldDescriptorProto_TYPE_ENUM, opt), ".p2.Closed"),
				withType(fld("grp", 6, descriptorpb.FieldDescriptorProto_TYPE_GROUP, opt), ".p2.P2.Grp"),
			},
			NestedType: []*descriptorpb.DescriptorProto{{Name: proto.String("Grp"),
				Field: []*descriptorpb.FieldDescriptorProto{fld("a", 7, i32, opt)}}},
		},
		&descriptorpb.DescriptorProto{Name: proto.String("G2"),
			Field: []*descriptorpb.FieldDescriptorProto{
				func() *descriptorpb.FieldDescriptorProto {
					f := fld("a", 1, i32, opt)
					f.OneofIndex = proto.Int32(0)
					return f
				}(),
				func() *descriptorpb.FieldDescriptorProto {
					f := withType(fld("g", 2, descriptorpb.FieldDescriptorProto_TYPE_GROUP, opt), ".p2.G2.G")
					f.OneofIndex = proto.Int32(0)
					return f
				}(),
			},
			OneofDecl: []*descriptorpb.OneofDescriptorProto{{Name: proto.String("u")}},
			NestedType: []*descriptorpb.DescriptorProto{{Name: proto.String("G"),
				Field: []*descriptorpb.FieldDescriptorProto{fld("b", 3, i32, opt)}}}},
		&descriptorpb.DescriptorProto{Name: proto.String("Ext"),
			ExtensionRange: []*descriptorpb.DescriptorProto_ExtensionRange{{Start: proto.Int32(100), End: proto.Int32(200)}}})
	p2.EnumType = []*descriptorpb.EnumDescriptorProto{{Name: proto.String("Closed"),
		Value: []*descriptorpb.EnumValueDescriptorProto{{Name: proto.String("CLOSED_A"), Number: proto.Int32(1)}}}}
	ed := refusedFile("ed", "editions", &descriptorpb.DescriptorProto{Name: proto.String("Ed"),
		Field: []*descriptorpb.FieldDescriptorProto{fld("x", 1, i32, opt)}})
	optF := fld("x", 1, i32, opt)
	optF.Proto3Optional = proto.Bool(true)
	optF.OneofIndex = proto.Int32(0)
	oneA, oneB := fld("a", 1, i32, opt), fld("b", 2, descriptorpb.FieldDescriptorProto_TYPE_STRING, opt)
	oneA.OneofIndex, oneB.OneofIndex = proto.Int32(0), proto.Int32(0)
	mapF := withType(fld("m", 1, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, rep), ".p3.Mp.MEntry")
	unp := fld("xs", 1, i32, rep)
	unp.Options = &descriptorpb.FieldOptions{Packed: proto.Bool(false)}
	lazy := withType(fld("s", 1, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, opt), ".p3.Ok")
	lazy.Options = &descriptorpb.FieldOptions{Lazy: proto.Bool(true)}
	p3 := refusedFile("p3", "proto3",
		&descriptorpb.DescriptorProto{Name: proto.String("Opt"), Field: []*descriptorpb.FieldDescriptorProto{optF},
			OneofDecl: []*descriptorpb.OneofDescriptorProto{{Name: proto.String("_x")}}},
		&descriptorpb.DescriptorProto{Name: proto.String("One"), Field: []*descriptorpb.FieldDescriptorProto{oneA, oneB},
			OneofDecl: []*descriptorpb.OneofDescriptorProto{{Name: proto.String("u")}}},
		&descriptorpb.DescriptorProto{Name: proto.String("Mp"), Field: []*descriptorpb.FieldDescriptorProto{mapF},
			NestedType: []*descriptorpb.DescriptorProto{{Name: proto.String("MEntry"),
				Field: []*descriptorpb.FieldDescriptorProto{
					fld("key", 1, descriptorpb.FieldDescriptorProto_TYPE_STRING, opt), fld("value", 2, i32, opt)},
				Options: &descriptorpb.MessageOptions{MapEntry: proto.Bool(true)}}}},
		&descriptorpb.DescriptorProto{Name: proto.String("Fl"), Field: []*descriptorpb.FieldDescriptorProto{
			fld("f", 1, descriptorpb.FieldDescriptorProto_TYPE_FLOAT, opt),
			fld("d", 2, descriptorpb.FieldDescriptorProto_TYPE_DOUBLE, rep)}},
		&descriptorpb.DescriptorProto{Name: proto.String("Unp"), Field: []*descriptorpb.FieldDescriptorProto{unp}},
		&descriptorpb.DescriptorProto{Name: proto.String("Lz"), Field: []*descriptorpb.FieldDescriptorProto{lazy}},
		&descriptorpb.DescriptorProto{Name: proto.String("Ok"), Field: []*descriptorpb.FieldDescriptorProto{fld("x", 1, i32, opt)}},
		&descriptorpb.DescriptorProto{Name: proto.String("Ind"), Field: []*descriptorpb.FieldDescriptorProto{
			withType(fld("p", 1, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, opt), ".p2.P2")}})
	p3.Dependency = []string{p2.GetName()}
	s.protocGenGo(t, dir, []*descriptorpb.FileDescriptorProto{p2, ed, p3}, "")
	opq := refusedFile("opq", "proto3", &descriptorpb.DescriptorProto{Name: proto.String("Opq"),
		Field: []*descriptorpb.FieldDescriptorProto{fld("x", 1, i32, opt)}})
	s.protocGenGo(t, dir, []*descriptorpb.FileDescriptorProto{opq}, ",default_api_level=API_OPAQUE")

	toml := `[protobuf]
imports = { p2 = "pbgenrand.tmp/p2", ed = "pbgenrand.tmp/ed", p3 = "pbgenrand.tmp/p3", opq = "pbgenrand.tmp/opq" }
roots = ["p2.P2", "p2.G2", "p2.Ext", "ed.Ed", "p3.Opt", "p3.One", "p3.Mp", "p3.Fl", "p3.Unp", "p3.Lz", "p3.Ind", "opq.Opq"]
`
	tomlPath := filepath.Join(dir, "protobuf.toml")
	must(t, os.WriteFile(tomlPath, []byte(toml), 0o644))
	out, code := runCode(dir, nil, "python3", s.pbgen, tomlPath, filepath.Join(dir, "codec"), "--pkg", "codec")
	if code != 2 {
		t.Fatalf("pbgen: exit %d, not 2 (refused):\n%s", code, out)
	}
	if _, err := os.Stat(filepath.Join(dir, "codec")); err == nil {
		t.Fatalf("pbgen wrote files for a refused schema")
	}
	for _, want := range []string{
		"field p2.P2.grp (number 6): a group",
		"field p2.G2.g (number 2): a group",
		"message p2.Ext (p2/p2.proto): extension ranges",
		"message ed.Ed (ed/ed.proto): a editions file",
		"message p3.Mp.MEntry (p3/p3.proto): a map entry",
		"field p3.Mp.m (number 1): a map",
		"field p3.Fl.f (number 1): float",
		"field p3.Fl.d (number 2): double",
		"field p3.Lz.s (number 1): weak or lazy",
		"field opq.Opq.x (number 1): no exported Go struct field",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("pbgen's refusal does not say %q:\n%s", want, out)
		}
	}
	// and nothing about the messages and fields inside the subset (since 2026-11-23: proto2's
	// explicit presence, required fields, defaults and closed enums; proto3 `optional`; oneofs;
	// unpacked repeated scalars)
	for _, ok := range []string{"p3.Ok ", "p3.Ok.", "p3.Ind", "p2.P2.x ", "p2.P2.r ", "p2.P2.d ", "p2.P2.c ",
		"p2.Closed", "p2.G2.a ", "p3.Opt", "p3.One", "p3.Unp", "ed.Ed.x "} {
		if strings.Contains(out, ok) {
			t.Errorf("pbgen refuses %s, inside the subset:\n%s", ok, out)
		}
	}
	t.Logf("refused as expected:\n%s", out)
}
