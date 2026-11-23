// Package jsongenrand is the differential test of the encoding/json codec generator
// (models/json/jsongen.py) over random Go types: each run writes a Go module with random types of
// the generator's subset (named structs with fields of every accepted kind and tag form: integers
// of every size with and without the string option, strings, bools, named basic types, slices,
// named and recursive slices, nested structs, any, json.RawMessage, omitempty, ignored and
// unexported fields, names with punctuation, names the generated code also uses), runs jsongen on
// it (its dump by reflection included) with some of the types as roots (an unnamed struct among
// them), and runs the generated regression test, which checks the codec against the real
// encoding/json (encodings of random values; decodings of encodings and their mutations into every
// type, fresh and pre-filled). Since 2026-11-23 also embedded structs (exported, unexported, by
// pointer, repeated, self-embedded, with colliding names), pointers, and types with their own
// MarshalJSON/UnmarshalJSON in every context, whose calls are logged and compared in order.
// TestRefusals checks one input per construct outside the subset is refused, naming it;
// TestAccepted the formerly refused constructs; TestReceiversAndCycles the review's cases.
//
// JSONGEN_RAND_TYPES (default 6) modules per run, JSONGEN_RAND_SEED (default 1) the first seed,
// JSONGEN_TEST_SCALE the generated tests' scale.
package jsongenrand

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
)

type setup struct {
	jsongen, modRoot string
}

func newSetup(t *testing.T) setup {
	wd, err := os.Getwd()
	must(t, err)
	modRoot := filepath.Clean(filepath.Join(wd, "..", ".."))
	gen := filepath.Join(modRoot, "json", "jsongen.py")
	if _, err := os.Stat(gen); err != nil {
		t.Skipf("no jsongen.py: %v", err)
	}
	if _, err := exec.LookPath("python3"); err != nil {
		t.Skip("no python3")
	}
	return setup{gen, modRoot}
}

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

func runCode(dir string, env []string, name string, args ...string) (string, int) {
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	cmd.Env = append(append(os.Environ(), "GOWORK=off", "GOPROXY=off", "GOFLAGS=-mod=mod"), env...)
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

// module writes a Go module jsongenrand.tmp into dir (importing models.lab) with package t
// holding src, and the [json] input naming the roots.
func (s setup) module(t *testing.T, dir, src string, roots []string) {
	t.Helper()
	gomod := fmt.Sprintf("module jsongenrand.tmp\n\ngo 1.27\n\nrequire models.lab v0.0.0-00010101000000-000000000000\n\n"+
		"replace models.lab => %s\n", s.modRoot)
	must(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(gomod), 0o644))
	sum, err := os.ReadFile(filepath.Join(s.modRoot, "go.sum"))
	must(t, err)
	must(t, os.WriteFile(filepath.Join(dir, "go.sum"), sum, 0o644))
	must(t, os.MkdirAll(filepath.Join(dir, "t"), 0o755))
	must(t, os.WriteFile(filepath.Join(dir, "t", "t.go"), []byte(src), 0o644))
	var q []string
	for _, x := range roots {
		q = append(q, "'"+x+"'")
	}
	toml := fmt.Sprintf("[json]\nimports = { t = \"jsongenrand.tmp/t\" }\nroots = [%s]\n", strings.Join(q, ", "))
	must(t, os.WriteFile(filepath.Join(dir, "json.toml"), []byte(toml), 0o644))
}

// gen writes random type declarations.
// gen writes random type declarations.
type gen struct {
	r     *rand.Rand
	decls []string
	named []string // the named types declared that the codec can name (for roots)
	n     int
	// constructs generated (logged)
	cEmbed, cHidden, cEmbedPtr, cPtr, cMethods, cSelfEmbed, cReuse int
	embeddable                                                     []string // exported struct types declared without methods (to embed again)
	noSelf                                                         bool     // declaring a method type's fields: no self-embedding
	hidden                                                         []string // unexported struct types (embedded only)
}

var ints = []string{"int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64"}
var basics = append(append([]string{}, ints...), "bool", "string")

// fieldNames include names the generated code also uses as identifiers, and few enough that the
// fields promoted from embedded structs collide (equal and case-equal names).
var fieldNames = []string{"A", "B", "P", "K", "V", "X", "E", "Ok", "N", "Data", "Err", "First", "Key",
	"More", "Empty", "Type", "ID", "Id", "D", "S", "Seq", "View_Num", "Len"}

// tagNames: JSON names drawn often, so that tagged fields collide with each other and with Go names.
var tagNames = []string{"a", "A", "id", "ID", "x", "X", "Data", "data", "k"}

// jsonNameChars: the characters of an accepted JSON name.
const jsonNameChars = "abcxyzABCXYZ019_-@.$:/!#%()*+;=?[]^{|}~ "

func (g *gen) name() string {
	g.n++
	return fmt.Sprintf("T%d", g.n)
}

func (g *gen) basic() string { return basics[g.r.Intn(len(basics))] }

func noBytes(e, ek string, g *gen) string {
	if (ek == "int" || ek == "method") && (e == "uint8" || strings.HasSuffix(g.under(e), "uint8")) {
		return "uint16"
	}
	return e
}

// typ returns a type expression (its kind for the string option: "int" for integer kinds).
func (g *gen) typ(depth int) (string, string) {
	k := g.r.Intn(16)
	if depth > 2 {
		k = g.r.Intn(4)
	}
	switch k {
	case 0, 1:
		b := g.basic()
		if strings.Contains(b, "int") {
			return b, "int"
		}
		return b, b
	case 2:
		n := g.name()
		b := g.basic()
		g.decls = append(g.decls, fmt.Sprintf("type %s %s", n, b))
		g.named = append(g.named, n)
		if strings.Contains(b, "int") {
			return n, "int"
		}
		return n, b
	case 3:
		if g.r.Intn(2) == 0 {
			return "any", "any"
		}
		return "json.RawMessage", "raw"
	case 4, 5:
		e, ek := g.typ(depth + 1)
		return "[]" + noBytes(e, ek, g), "slice"
	case 6:
		n := g.name()
		e, ek := g.typ(depth + 1)
		g.decls = append(g.decls, fmt.Sprintf("type %s []%s", n, noBytes(e, ek, g)))
		g.named = append(g.named, n)
		return n, "slice"
	case 7:
		n := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s []%s", n, n))
		g.named = append(g.named, n)
		return n, "slice"
	case 8, 9:
		// a pointer to a type that is neither a pointer nor an interface
		for {
			e, ek := g.typ(depth + 1)
			if ek != "any" && ek != "ptr" {
				g.cPtr++
				return "*" + e, "ptr"
			}
		}
	case 10, 11:
		return g.method(depth + 1), "method"
	default:
		return g.strct(depth + 1), "struct"
	}
}

// under: the declared underlying type of a named basic type, through named types (else "").
func (g *gen) under(n string) string {
	for _, d := range g.decls {
		if strings.HasPrefix(d, "type "+n+" ") {
			u := strings.TrimPrefix(d, "type "+n+" ")
			if v := g.under(u); v != "" {
				return v
			}
			return u
		}
	}
	return ""
}

func (g *gen) jsonName() string {
	if g.r.Intn(2) == 0 {
		return tagNames[g.r.Intn(len(tagNames))]
	}
	n := 1 + g.r.Intn(6)
	var sb strings.Builder
	for i := 0; i < n; i++ {
		sb.WriteByte(jsonNameChars[g.r.Intn(len(jsonNameChars))])
	}
	s := sb.String()
	if s == "-" {
		return "dash"
	}
	return s
}

// fields returns random field declarations of a struct type n; hidden: the struct is unexported
// and embedded only, its Go field names unique in the whole package (so that Go's promotion of
// them through it is unambiguous).
func (g *gen) fields(n string, depth int, hidden bool) []string {
	var fs []string
	used := map[string]bool{} // Go names
	nf := g.r.Intn(7)
	for i := 0; i < nf; i++ {
		f := fieldNames[g.r.Intn(len(fieldNames))]
		if hidden {
			g.n++
			f = fmt.Sprintf("H%d", g.n)
		}
		if used[f] {
			continue
		}
		ty, kind := g.typ(depth)
		if g.r.Intn(8) == 0 && depth < 3 && !hidden {
			ty, kind = "[]"+n, "slice" // the struct's own type, through a slice
		}
		tag := ""
		switch g.r.Intn(7) {
		case 0, 6:
			// no tag: the Go name
		case 1:
			tag = g.jsonName()
		case 2:
			tag = ",omitempty"
		case 3:
			tag = g.jsonName() + ",omitempty"
		case 4:
			if kind == "int" {
				tag = g.jsonName() + ",string"
				if g.r.Intn(2) == 0 {
					tag = g.jsonName() + ",omitempty,string"
				}
			}
		case 5:
			if g.r.Intn(3) == 0 {
				tag = "-"
			}
		}
		used[f] = true
		if tag != "" {
			fs = append(fs, fmt.Sprintf("\t%s %s `json:%q`", f, ty, tag))
		} else {
			fs = append(fs, fmt.Sprintf("\t%s %s", f, ty))
		}
	}
	// embedded structs: exported (by value or pointer), unexported by value, an exported type
	// declared before (embedded again: Go's breadth-first walk sees it twice), the type itself
	// through a pointer
	if depth < 3 {
		for e := g.r.Intn(4) - 1; e > 0 || (e == 0 && g.r.Intn(2) == 0); e-- {
			switch g.r.Intn(6) {
			case 0, 1:
				en := g.embedStruct(depth+1, false)
				if g.r.Intn(3) == 0 {
					g.cEmbedPtr++
					fs = append(fs, "\t*"+en)
				} else {
					g.cEmbed++
					fs = append(fs, "\t"+en)
				}
			case 2, 3:
				g.cHidden++
				fs = append(fs, "\t"+g.embedStruct(depth+1, true))
			case 4:
				if len(g.embeddable) > 0 {
					g.cReuse++
					en := g.embeddable[g.r.Intn(len(g.embeddable))]
					if g.r.Intn(2) == 0 {
						fs = append(fs, "\t*"+en)
					} else if !g.contains(en, n) {
						fs = append(fs, "\t"+en)
					}
				}
			case 5:
				if !hidden && !g.noSelf {
					g.cSelfEmbed++
					fs = append(fs, "\t*"+n)
				}
			}
		}
	}
	if g.r.Intn(3) == 0 {
		g.n++
		fs = append(fs, fmt.Sprintf("\thidden%d int", g.n))
	}
	return dedupeEmbeds(fs)
}

// contains: whether struct type a's declaration (transitively, through embedding by value)
// names b (embedding b's container by value into b would be a cycle).
func (g *gen) contains(a, b string) bool {
	return a == b // types are declared before they are embedded: only self-embedding cycles
}

func dedupeEmbeds(fs []string) []string {
	seen := map[string]bool{}
	var out []string
	for _, f := range fs {
		k := strings.TrimPrefix(strings.TrimSpace(f), "*")
		if !strings.Contains(k, " ") {
			if seen[k] {
				continue // one embedded field per type name
			}
			seen[k] = true
		}
		out = append(out, f)
	}
	return out
}

// embedStruct declares a struct type to embed: exported (also usable elsewhere) or unexported.
func (g *gen) embedStruct(depth int, hidden bool) string {
	g.n++
	n := fmt.Sprintf("E%d", g.n)
	if hidden {
		n = fmt.Sprintf("e%d", g.n)
	}
	fs := g.fields(n, depth, hidden)
	g.decls = append(g.decls, fmt.Sprintf("type %s struct {\n%s\n}", n, strings.Join(fs, "\n")))
	if hidden {
		g.hidden = append(g.hidden, n)
	} else {
		g.named = append(g.named, n)
		g.embeddable = append(g.embeddable, n)
	}
	return n
}

func (g *gen) strct(depth int) string {
	n := g.name()
	fs := g.fields(n, depth, false)
	g.decls = append(g.decls, fmt.Sprintf("type %s struct {\n%s\n}", n, strings.Join(fs, "\n")))
	g.named = append(g.named, n)
	g.embeddable = append(g.embeddable, n)
	return n
}

// method declares a type with its own MarshalJSON and/or UnmarshalJSON (value or pointer
// receivers): a struct, a named slice, a named integer or string, over an unexported plain type
// pT without methods. Every call is logged in CallLog (the generated test compares the calls the
// real encoding/json makes with the codec's). The bodies: the plain value's real encoding, with
// whitespace around it, a fixed value, invalid output (nil, empty, cut), an error, nesting at the
// limit; decoding into the plain value (merging), recording the bytes, failing on some.
func (g *gen) method(depth int) string {
	g.cMethods++
	n := g.name()
	p := "p" + n
	var under string
	kind := g.r.Intn(4)
	switch kind {
	case 0:
		save := g.noSelf
		g.noSelf = true
		under = "struct {\n" + strings.Join(g.fields(n, depth, false), "\n") + "\n}"
		g.noSelf = save
	case 1:
		e, ek := g.typ(depth + 1)
		under = "[]" + noBytes(e, ek, g)
	case 2:
		under = ints[g.r.Intn(len(ints))]
	default:
		under = "string"
	}
	g.decls = append(g.decls, fmt.Sprintf("type %s %s", p, under), fmt.Sprintf("type %s %s", n, p))
	g.named = append(g.named, n)
	menc := g.r.Intn(3) // 0: none, 1: value receiver, 2: pointer receiver
	mdec := g.r.Intn(3) // 0: none, 1: pointer receiver, 2: value receiver
	if menc == 0 && mdec == 0 {
		menc = 1 + g.r.Intn(2)
	}
	if menc > 0 {
		recv, val, tag := "x "+n, p+"(x)", "v"
		if menc == 2 {
			recv, val, tag = "x *"+n, p+"(*x)", "p"
		}
		var body string
		switch {
		case kind >= 2 && g.r.Intn(2) == 0:
			body = fmt.Sprintf("return []byte(strconv.Quote(fmt.Sprint(%s))), nil", val)
		default:
			switch g.r.Intn(8) {
			case 0, 1:
				body = fmt.Sprintf("return json.Marshal(%s)", val)
			case 2:
				body = fmt.Sprintf("b, err := json.Marshal(%s)\n\treturn append(append([]byte(\" [ \\\"%s\\\" ,\\n\"), b...), \" ] \"...), err", val, n)
			case 3:
				body = "return []byte(`{\"k\" : [ true , null , -1.5e3, \"a b\" ] }`), nil"
			case 4:
				body = fmt.Sprintf("if len(fmt.Sprint(%s))%%3 == 0 {\n\t\treturn nil, errors.New(%q)\n\t}\n\treturn json.Marshal(%s)", val, n, val)
			case 5:
				body = fmt.Sprintf("switch len(fmt.Sprint(%s)) %% 3 {\n\tcase 0:\n\t\treturn nil, nil\n\tcase 1:\n\t\treturn []byte(\"\"), nil\n\t}\n\treturn []byte(\"[1, {\"), nil", val)
			case 6:
				body = "return []byte(strings.Repeat(\"[\", 9997) + strings.Repeat(\"]\", 9997)), nil"
			default:
				body = fmt.Sprintf("return []byte(\" \\t\" + strconv.Itoa(len(fmt.Sprint(%s))) + \"\\n\"), nil", val)
			}
		}
		g.decls = append(g.decls, fmt.Sprintf("func (%s) MarshalJSON() ([]byte, error) {\n\tCallLog = append(CallLog, \"%s.MarshalJSON/%s\")\n\t%s\n}", recv, n, tag, body))
	}
	if mdec > 0 {
		recv, tag := "x *"+n, "p"
		var body string
		if mdec == 2 {
			recv, tag = "x "+n, "v"
			body = "if len(b)%2 == 0 {\n\t\treturn errors.New(\"odd\")\n\t}\n\treturn nil"
		} else if kind == 2 {
			body = fmt.Sprintf("*x = %s(len(b))\n\treturn nil", n)
		} else if kind == 3 {
			body = fmt.Sprintf("*x = %s(strconv.Itoa(len(b)))\n\treturn nil", n)
		} else {
			switch g.r.Intn(3) {
			case 0:
				body = fmt.Sprintf("v := %s(*x)\n\terr := json.Unmarshal(b, &v)\n\t*x = %s(v)\n\treturn err", p, n)
			case 1:
				body = fmt.Sprintf("if b[0] == '[' || len(b)%%4 == 0 {\n\t\treturn errors.New(%q)\n\t}\n\tv := %s(*x)\n\terr := json.Unmarshal(b, &v)\n\t*x = %s(v)\n\treturn err", n, p, n)
			default:
				body = "return nil"
			}
		}
		g.decls = append(g.decls, fmt.Sprintf("func (%s) UnmarshalJSON(b []byte) error {\n\tCallLog = append(CallLog, \"%s.UnmarshalJSON/%s \"+string(b))\n\t%s\n}", recv, n, tag, body))
	}
	return n
}

// source returns a package t with random types, and the roots.
func source(seed int64) (string, []string, *gen) {
	g := &gen{r: rand.New(rand.NewSource(seed))}
	var roots []string
	for i := 0; i < 1+g.r.Intn(4); i++ {
		roots = append(roots, "t."+g.strct(0))
	}
	if g.r.Intn(2) == 0 {
		// a method type in every context: a field by value and by pointer, a slice element, an any
		m := g.method(1)
		w := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s struct {\n\tV %s\n\tP *%s\n\tS []%s\n\tA any\n}", w, m, m, m))
		g.named = append(g.named, w)
		roots = append(roots, "t."+w, "t."+m)
	}
	for _, n := range g.named {
		if g.r.Intn(3) == 0 {
			roots = append(roots, "t."+n)
		}
	}
	if g.r.Intn(2) == 0 {
		roots = append(roots, "[]t."+g.strct(0))
	}
	if g.r.Intn(2) == 0 {
		roots = append(roots, `struct { A uint64 "json:\"a,string\""; R json.RawMessage "json:\"r\"" }`)
	}
	roots = dedupe(roots)
	src := "package t\n\nimport (\n\t\"encoding/json\"\n\t\"errors\"\n\t\"fmt\"\n\t\"strconv\"\n\t\"strings\"\n)\n\n" +
		"var _ json.RawMessage\nvar _ = errors.New\nvar _ = fmt.Sprint\nvar _ = strconv.Itoa\nvar _ = strings.Repeat\n\n" +
		"// CallLog: the JSON methods called, in order.\nvar CallLog []string\n\n" +
		strings.Join(g.decls, "\n\n") + "\n"
	return src, roots, g
}

func dedupe(xs []string) []string {
	seen := map[string]bool{}
	var out []string
	for _, x := range xs {
		if !seen[x] {
			seen[x] = true
			out = append(out, x)
		}
	}
	return out
}

// callsTest: a test file of the codec package that makes the generated tests compare the methods
// called (jsongen_testgen.py's jtCallLog, jtCallReset).
const callsTest = `package codec

import tt "jsongenrand.tmp/t"

func init() {
	jtCallLog = func() []string { return tt.CallLog }
	jtCallReset = func() { tt.CallLog = nil }
}
`

var statsRe = regexp.MustCompile(`JSONGEN-STATS types=(\d+) enc_equal=(\d+) enc_err=(\d+) enc_panic=(\d+) dec_equal=(\d+) dec_err=(\d+) dec_syntax=(\d+) dec_panic=(\d+) calls=(\d+)`)

func TestRandomTypes(t *testing.T) {
	s := newSetup(t)
	n, _ := strconv.Atoi(os.Getenv("JSONGEN_RAND_TYPES"))
	if n <= 0 {
		n = 6
	}
	seed0, _ := strconv.ParseInt(os.Getenv("JSONGEN_RAND_SEED"), 10, 64)
	if seed0 == 0 {
		seed0 = 1
	}
	var tot [9]int
	var cons [7]int
	for i := 0; i < n; i++ {
		seed := seed0 + int64(i)
		src, roots, g := source(seed)
		for k, c := range []int{g.cEmbed, g.cEmbedPtr, g.cHidden, g.cReuse, g.cSelfEmbed, g.cPtr, g.cMethods} {
			cons[k] += c
		}
		dir := t.TempDir()
		s.module(t, dir, src, roots)
		out, code := runCode(dir, nil, "python3", s.jsongen, "json.toml", "codec", "--pkg", "codec")
		if code != 0 {
			t.Fatalf("seed %d: jsongen: exit %d\n%s\n%s\nroots %q", seed, code, out, src, roots)
		}
		must(t, os.WriteFile(filepath.Join(dir, "codec", "calls_test.go"), []byte(callsTest), 0o644))
		out, code = runCode(dir, []string{fmt.Sprintf("JSONGEN_TEST_SEED=%d", seed)}, "go", "test", "-count=1", "-v", "./codec")
		if code != 0 {
			t.Fatalf("seed %d: the generated test failed:\n%s\n%s\nroots %q", seed, out, src, roots)
		}
		for idx, m := range statsRe.FindAllStringSubmatch(out, -1) {
			for k := 1; k < len(m); k++ {
				x, _ := strconv.Atoi(m[k])
				if k > 1 || idx == 0 {
					tot[k-1] += x
				}
			}
		}
	}
	t.Logf("%d modules, %d types (embedded %d, embedded pointers %d, unexported embedded %d, embedded again %d, "+
		"self-embedded %d, pointers %d, types with JSON methods %d): encodings equal %d, errors agreed %d, "+
		"NotModelled %d; decodings equal %d, errors agreed %d, syntax errors agreed %d, NotModelled %d; "+
		"method calls agreed %d",
		n, tot[0], cons[0], cons[1], cons[2], cons[3], cons[4], cons[5], cons[6], tot[1], tot[2], tot[3], tot[4],
		tot[5], tot[6], tot[7], tot[8])
}

// One input per construct outside the subset: refused (exit 2), naming it.
func TestRefusals(t *testing.T) {
	s := newSetup(t)
	cases := []struct{ name, decls, root, want string }{
		{"float64", "type A struct{ F float64 }", "t.A", "kind float64"},
		{"float32", "type A struct{ F float32 }", "t.A", "kind float32"},
		{"complex", "type A struct{ F complex128 }", "t.A", "kind complex128"},
		{"chan", "type A struct{ F chan int }", "t.A", "kind chan"},
		{"func", "type A struct{ F func() }", "t.A", "kind func"},
		{"uintptr", "type A struct{ F uintptr }", "t.A", "kind uintptr"},
		{"array", "type A struct{ F [2]int }", "t.A", "kind array"},
		{"map", "type A struct{ F map[string]int }", "t.A", "kind map"},
		{"map-int-key", "type A struct{ F map[int]string }", "t.A", "kind map"},
		{"pointer-root", "type A struct{ F int }", "*t.A", "a pointer type"},
		{"pointer-pointer", "type A struct{ F **int }", "t.A", "a pointer to a ptr"},
		{"pointer-interface", "type A struct{ F *any }", "t.A", "a pointer to a interface"},
		{"named-pointer", "type P *int\ntype A struct{ F P }", "t.A", "a named pointer type"},
		{"string-on-pointer", "type A struct{ F *int `json:\"f,string\"` }", "t.A", "string option on a ptr"},
		{"interface", "type A struct{ F error }", "t.A", "has methods"},
		{"any-root", "type A struct{ F int }", "any", "any as a root"},
		{"bytes", "type A struct{ F []byte }", "t.A", "uint8 kind"},
		{"named-bytes", "type K uint8\ntype A struct{ F []K }", "t.A", "uint8 kind"},
		{"embedded-unexported-pointer", "type e struct{ X int }\ntype A struct{ *e }", "t.A", "unexported embedded pointer"},
		{"embedded-with-methods", "type E struct{ X int }\nfunc (*E) UnmarshalJSON([]byte) error { return nil }\ntype A struct{ E; Y int }\nfunc (*A) UnmarshalJSON([]byte) error { return nil }", "t.A", "embedded"},
		{"embedded-options", "type E struct{ X int }\ntype A struct{ E `json:\",omitempty\"` }", "t.A", "tag options on an embedded field"},
		{"embedded-unexported-named", "type e struct{ X int }\ntype A struct{ e `json:\"e\"` }", "t.A", "unexported embedded struct with a JSON name"},
		{"promoted-selector", "type e struct{ X int }\ntype A struct{ e; X int `json:\"y\"` }", "t.A", "selector .X"},
		{"promoted-method", "type e struct{ X int }\ntype A struct{ e }\nfunc (A) X() {}", "t.A", "selector .X"},
		{"unexported-tag", "type A struct{ x int `json:\"x\"` }", "t.A", "unexported field with tag"},
		{"html-name", "type A struct{ F int `json:\"a<b\"` }", "t.A", "a character outside"},
		{"amp-name", "type A struct{ F int `json:\"a&b\"` }", "t.A", "a character outside"},
		{"non-ascii-name", "type A struct{ F int `json:\"é\"` }", "t.A", "a character outside"},
		{"non-ascii-go-name", "type A struct{ Ä int }", "t.A", "not ASCII"},
		{"quoted-name", "type A struct{ F int `json:\"'q'\"` }", "t.A", "a character outside"},
		{"unknown-option", "type A struct{ F int `json:\"a,foo\"` }", "t.A", "tag option 'foo'"},
		{"omitzero", "type A struct{ F int `json:\"a,omitzero\"` }", "t.A", "tag option 'omitzero'"},
		{"inline", "type A struct{ F int `json:\",inline\"` }", "t.A", "tag option 'inline'"},
		{"empty-option", "type A struct{ F int `json:\"-,\"` }", "t.A", "tag option ''"},
		{"repeated-option", "type A struct{ F int `json:\"a,omitempty,omitempty\"` }", "t.A", "repeated"},
		{"string-on-string", "type A struct{ F string `json:\"a,string\"` }", "t.A", "string option on a string"},
		{"string-on-bool", "type A struct{ F bool `json:\"a,string\"` }", "t.A", "string option on a bool"},
		{"string-on-method-type", "type K int\nfunc (K) MarshalJSON() ([]byte, error) { return nil, nil }\ntype A struct{ F K `json:\"f,string\"` }", "t.A", "string option on a int"},
		{"number", "type A struct{ F json.Number }", "t.A", "Number"},
		{"marshal-json-signature", "type A struct{ X int }\nfunc (A) MarshalJSON() []byte { return nil }", "t.A", "does not implement Marshaler"},
		{"unmarshal-json-signature", "type A struct{ X int }\nfunc (*A) UnmarshalJSON(string) error { return nil }", "t.A", "does not implement Unmarshaler"},
		{"marshal-text", "type K int\nfunc (K) MarshalText() ([]byte, error) { return nil, nil }\ntype A struct{ F K }", "t.A", "TextMarshaler"},
		{"marshal-text-ptr-json", "type K int\nfunc (K) MarshalText() ([]byte, error) { return nil, nil }\nfunc (*K) MarshalJSON() ([]byte, error) { return nil, nil }\ntype A struct{ F K }", "t.A", "TextMarshaler"},
		{"append-text", "type K string\nfunc (K) AppendText(b []byte) ([]byte, error) { return b, nil }\ntype A struct{ F []K }", "t.A", "TextAppender"},
		{"unmarshal-text", "type K string\nfunc (*K) UnmarshalText([]byte) error { return nil }\ntype A struct{ F K }", "t.A", "TextUnmarshaler"},
		{"marshal-json-to", "type A struct{ X int }\nfunc (A) MarshalJSONTo() error { return nil }", "t.A", "MarshalJSONTo"},
		{"unmarshal-json-from", "type A struct{ X int }\nfunc (*A) UnmarshalJSONFrom() error { return nil }", "t.A", "UnmarshalJSONFrom"},
		{"method-type-structure", "type K struct{ F float64 }\nfunc (*K) MarshalJSON() ([]byte, error) { return nil, nil }\nfunc (*K) UnmarshalJSON([]byte) error { return nil }\ntype A struct{ F K }", "t.A", "kind float64"},
		{"unexported-type", "type b int\ntype A struct{ F b }", "t.A", "unexported"},
		{"generic", "type G[T any] struct{ X T }\ntype A struct{ F G[int] }", "t.A", "generic"},
		{"unnamed-field-struct", "type A struct{ F struct{ X int } }", "t.A", "unnamed struct"},
		{"unknown-package", "type A struct{ F os.FileMode }", "t.A", "has no alias"},
	}
	for _, c := range cases {
		dir := t.TempDir()
		src := fmt.Sprintf("package t\n\n%s\n%s\n", refusalImports, c.decls)
		s.module(t, dir, src, []string{c.root})
		out, code := runCode(dir, nil, "python3", s.jsongen, "json.toml", "codec", "--pkg", "codec")
		if code != 2 || !strings.Contains(out, c.want) {
			t.Errorf("%s: jsongen exit %d, want 2 naming %q:\n%s", c.name, code, c.want, out)
		}
		if _, err := os.Stat(filepath.Join(dir, "codec")); err == nil {
			t.Errorf("%s: a refused input wrote files", c.name)
		}
	}
}

const refusalImports = "import (\n\t\"encoding/json\"\n\t\"os\"\n)\n\nvar _ json.RawMessage\nvar _ os.FileMode\n"

// The constructs the 2026-11-23 extension accepts (formerly refused): accepted, and the generated
// test passes against the real encoding/json.
func TestAccepted(t *testing.T) {
	s := newSetup(t)
	cases := []struct{ name, decls, root string }{
		{"pointer-field", "type A struct{ F *int; G *string `json:\",omitempty\"`; H *bool }", "t.A"},
		{"pointer-elem", "type B struct{ X int }\ntype A struct{ F []*int; G []*B; H *[]B }", "t.A"},
		{"embedded", "type E struct{ X int }\ntype A struct{ E; Y int }", "t.A"},
		{"embedded-ptr", "type E struct{ X int }\ntype A struct{ *E; Y int }", "t.A"},
		{"embedded-unexported", "type e struct{ X int `json:\"x\"` }\ntype A struct{ e; Y int }", "t.A"},
		{"embedded-self", "type A struct{ *A; X int }", "t.A"},
		{"embedded-twice", "type C struct{ Z int }\ntype B struct{ C; Y int }\ntype A struct{ B; C; X int }", "t.A"},
		{"same-name", "type A struct{ F int `json:\"a\"`; G int `json:\"a\"`; H int }", "t.A"},
		{"same-name-tagged", "type A struct{ F int; G int `json:\"F\"` }", "t.A"},
		{"fold-name", "type A struct{ F int `json:\"a\"`; G int `json:\"A\"` }", "t.A"},
		{"equal-depth", "type E1 struct{ A int; B int `json:\"b\"` }\ntype E2 struct{ A int `json:\"A\"`; B int `json:\"b\"`; C int }\ntype A struct{ E1; E2 }", "t.A"},
		{"marshal-json", "type A struct{ X int }\nfunc (a A) MarshalJSON() ([]byte, error) { return json.Marshal(a.X) }", "t.A"},
		{"unmarshal-json-ptr", "type A struct{ X int }\nfunc (a *A) UnmarshalJSON(b []byte) error { a.X = len(b); return nil }", "t.A"},
		{"marshal-json-ptr", "type K int\nfunc (k *K) MarshalJSON() ([]byte, error) { return []byte(\"[1]\"), nil }\ntype A struct{ V K; P *K; S []K; Y any }", "t.A"},
		{"shadowed-text", "type K struct{ M map[string]float64 }\nfunc (K) MarshalText() ([]byte, error) { return nil, nil }\nfunc (*K) UnmarshalText([]byte) error { return nil }\n" +
			"func (K) MarshalJSON() ([]byte, error) { return []byte(\"1\"), nil }\nfunc (*K) UnmarshalJSON([]byte) error { return nil }\ntype A struct{ F K; P *K }", "t.A"},
	}
	for _, c := range cases {
		dir := t.TempDir()
		src := fmt.Sprintf("package t\n\n%s\n%s\n", refusalImports, c.decls)
		s.module(t, dir, src, []string{c.root})
		out, code := runCode(dir, nil, "python3", s.jsongen, "json.toml", "codec", "--pkg", "codec")
		if code != 0 {
			t.Errorf("%s: jsongen exit %d, want 0:\n%s", c.name, code, out)
			continue
		}
		if out, code := runCode(dir, nil, "go", "test", "-count=1", "./codec"); code != 0 {
			t.Errorf("%s: the generated test failed:\n%s", c.name, out)
		}
	}
}

// Receivers and cycles (the independent review's findings, notes/axiom-review/jsongen.md): an
// UnmarshalJSON method runs on the slice element itself (its address, kept by the method, is the
// element's after decoding, as the real one's), and a cyclic value is a NotModelled panic in the
// codec where the real one reports a cycle.
func TestReceiversAndCycles(t *testing.T) {
	s := newSetup(t)
	dir := t.TempDir()
	src := "package t\n\n" + refusalImports + `
type SP struct {
	N    int
	self *SP
}

func (p *SP) UnmarshalJSON(b []byte) error { p.self = p; p.N = len(b); return nil }

// Self is the receiver the last UnmarshalJSON ran on.
func (p *SP) Self() *SP { return p.self }

type Holder struct {
	S []SP
	F SP
	P *SP
}

type ML int

func (m ML) MarshalJSON() ([]byte, error) { return []byte("1"), nil }

type Cyc struct {
	M    ML
	Next *Cyc
}
`
	s.module(t, dir, src, []string{"t.Holder", "t.Cyc"})
	out, code := runCode(dir, nil, "python3", s.jsongen, "json.toml", "codec", "--pkg", "codec")
	if code != 0 {
		t.Fatalf("jsongen: exit %d\n%s", code, out)
	}
	test := `package codec

import (
	"encoding/json"
	"testing"

	"models.lab/jsoncodec"
	tt "jsongenrand.tmp/t"
)

func TestReceivers(t *testing.T) {
	for _, in := range []string{` + "`" + `{"S":[1],"F":2,"P":3}` + "`" + `, ` + "`" + `{"S":[1, 22, 333, 4444, 5, 6, 7, 8, 9]}` + "`" + `} {
		var a, b tt.Holder
		if err := json.Unmarshal([]byte(in), &a); err != nil {
			t.Fatal(err)
		}
		if err := jsonUnmarshal([]byte(in), &b); err != nil {
			t.Fatal(err)
		}
		if len(a.S) != len(b.S) || cap(a.S) != cap(b.S) {
			t.Fatalf("%s: lengths or capacities differ: real %d/%d, codec %d/%d", in, len(a.S), cap(a.S), len(b.S), cap(b.S))
		}
		for i := range a.S {
			ra, rb := a.S[i].Self() == &a.S[i], b.S[i].Self() == &b.S[i]
			if ra != rb {
				t.Fatalf("%s: element %d: the receiver is the element: real %v, codec %v", in, i, ra, rb)
			}
		}
	}
}

func TestCycle(t *testing.T) {
	c := &tt.Cyc{}
	c.Next = c
	if _, err := json.Marshal(c); err == nil {
		t.Fatal("real: no error on a cycle")
	}
	defer func() {
		if _, ok := recover().(jsoncodec.NotModelled); !ok {
			t.Fatal("codec: no NotModelled panic on a cycle")
		}
	}()
	jsonMarshal(c)
}
`
	must(t, os.WriteFile(filepath.Join(dir, "codec", "receivers_test.go"), []byte(test), 0o644))
	if out, code := runCode(dir, nil, "go", "test", "-count=1", "./codec"); code != 0 {
		t.Fatalf("the tests failed:\n%s", out)
	}
}
