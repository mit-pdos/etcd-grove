// Package jsongenrand is the differential test of the encoding/json codec generator
// (models/json/jsongen.py) over random Go types: each run writes a Go module with random types of
// the generator's subset (named structs with fields of every accepted kind and tag form: integers
// of every size with and without the string option, strings, bools, named basic types, slices,
// named and recursive slices, nested structs, any, json.RawMessage, omitempty, ignored and
// unexported fields, names with punctuation, names the generated code also uses), runs jsongen on
// it (its dump by reflection included) with some of the types as roots (an unnamed struct among
// them), and runs the generated regression test, which checks the codec against the real
// encoding/json (encodings of random values; decodings of encodings and their mutations into every
// type, fresh and pre-filled). TestRefusals checks one input per construct outside the subset is
// refused, naming it.
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
type gen struct {
	r     *rand.Rand
	decls []string
	named []string // the named types declared (for roots)
	n     int
}

var ints = []string{"int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64"}
var basics = append(append([]string{}, ints...), "bool", "string")

// fieldNames include names the generated code also uses as identifiers.
var fieldNames = []string{"A", "B", "P", "K", "V", "X", "E", "Ok", "N", "Data", "Err", "First", "Key",
	"More", "Empty", "Type", "ID", "Id", "D", "S", "Seq", "View_Num", "Len"}

// jsonNameChars: the characters of an accepted JSON name.
const jsonNameChars = "abcxyzABCXYZ019_-@.$:/!#%()*+;=?[]^{|}~ "

func (g *gen) name() string {
	g.n++
	return fmt.Sprintf("T%d", g.n)
}

func (g *gen) basic() string { return basics[g.r.Intn(len(basics))] }

// typ returns a type expression (its kind for the string option: "int" for integer kinds).
func (g *gen) typ(depth int) (string, string) {
	k := g.r.Intn(12)
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
		if ek == "int" && (e == "uint8" || strings.HasSuffix(g.under(e), "uint8")) {
			e = "uint16"
		}
		return "[]" + e, "slice"
	case 6:
		n := g.name()
		e, ek := g.typ(depth + 1)
		if ek == "int" && (e == "uint8" || strings.HasSuffix(g.under(e), "uint8")) {
			e = "int"
		}
		g.decls = append(g.decls, fmt.Sprintf("type %s []%s", n, e))
		g.named = append(g.named, n)
		return n, "slice"
	case 7:
		n := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s []%s", n, n))
		g.named = append(g.named, n)
		return n, "slice"
	default:
		return g.strct(depth + 1), "struct"
	}
}

// under: the declared underlying type of a named basic type (else "").
func (g *gen) under(n string) string {
	for _, d := range g.decls {
		if strings.HasPrefix(d, "type "+n+" ") {
			return strings.TrimPrefix(d, "type "+n+" ")
		}
	}
	return ""
}

func (g *gen) jsonName() string {
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

func (g *gen) strct(depth int) string {
	n := g.name()
	var fs []string
	used := map[string]bool{}   // Go names
	folded := map[string]bool{} // JSON names, lower case
	nf := g.r.Intn(7)
	for i := 0; i < nf; i++ {
		f := fieldNames[g.r.Intn(len(fieldNames))]
		if used[f] {
			continue
		}
		ty, kind := g.typ(depth)
		if g.r.Intn(8) == 0 && depth < 3 {
			ty, kind = n, "self" // a field of the struct's own type is not allowed: use a slice
			ty = "[]" + n
			kind = "slice"
		}
		name := f
		tag := ""
		switch g.r.Intn(6) {
		case 0:
			// no tag: the Go name
		case 1:
			name = g.jsonName()
			tag = name
		case 2:
			tag = ",omitempty"
		case 3:
			name = g.jsonName()
			tag = name + ",omitempty"
		case 4:
			if kind == "int" {
				name = g.jsonName()
				tag = name + ",string"
				if g.r.Intn(2) == 0 {
					tag = name + ",omitempty,string"
				}
			}
		case 5:
			if g.r.Intn(3) == 0 {
				tag = "-"
				name = ""
			}
		}
		if name != "" && folded[strings.ToLower(name)] {
			continue
		}
		used[f] = true
		if name != "" {
			folded[strings.ToLower(name)] = true
		}
		if tag != "" {
			fs = append(fs, fmt.Sprintf("\t%s %s `json:%q`", f, ty, tag))
		} else {
			fs = append(fs, fmt.Sprintf("\t%s %s", f, ty))
		}
	}
	if g.r.Intn(3) == 0 {
		fs = append(fs, "\thidden int")
	}
	g.decls = append(g.decls, fmt.Sprintf("type %s struct {\n%s\n}", n, strings.Join(fs, "\n")))
	g.named = append(g.named, n)
	return n
}

// source returns a package t with random types, and the roots.
func source(seed int64) (string, []string) {
	g := &gen{r: rand.New(rand.NewSource(seed))}
	var roots []string
	for i := 0; i < 1+g.r.Intn(4); i++ {
		roots = append(roots, "t."+g.strct(0))
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
	src := "package t\n\nimport \"encoding/json\"\n\nvar _ json.RawMessage\n\n" + strings.Join(g.decls, "\n\n") + "\n"
	return src, roots
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

var statsRe = regexp.MustCompile(`JSONGEN-STATS types=(\d+) enc_equal=(\d+) enc_err=(\d+) enc_stuck=(\d+) dec_equal=(\d+) dec_err=(\d+) dec_syntax=(\d+) dec_stuck=(\d+)`)

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
	var tot [8]int
	for i := 0; i < n; i++ {
		seed := seed0 + int64(i)
		src, roots := source(seed)
		dir := t.TempDir()
		s.module(t, dir, src, roots)
		out, code := runCode(dir, nil, "python3", s.jsongen, "json.toml", "codec", "--pkg", "codec")
		if code != 0 {
			t.Fatalf("seed %d: jsongen: exit %d\n%s\n%s", seed, code, out, src)
		}
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
	t.Logf("%d modules, %d types: encodings equal %d, errors agreed %d, stuck (not modelled) %d; decodings equal %d, "+
		"errors agreed %d, syntax errors agreed %d, stuck (not modelled) %d",
		n, tot[0], tot[1], tot[2], tot[3], tot[4], tot[5], tot[6], tot[7])
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
		{"pointer-field", "type A struct{ F *int }", "t.A", "a pointer"},
		{"pointer-elem", "type A struct{ F []*int }", "t.A", "a pointer"},
		{"pointer-root", "type A struct{ F int }", "*t.A", "a pointer type"},
		{"interface", "type A struct{ F error }", "t.A", "has methods"},
		{"any-root", "type A struct{ F int }", "any", "any as a root"},
		{"bytes", "type A struct{ F []byte }", "t.A", "uint8 kind"},
		{"named-bytes", "type K uint8\ntype A struct{ F []K }", "t.A", "uint8 kind"},
		{"embedded", "type E struct{ X int }\ntype A struct{ E }", "t.A", "embedded"},
		{"embedded-ptr", "type E struct{ X int }\ntype A struct{ *E }", "t.A", "embedded"},
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
		{"same-name", "type A struct{ F int `json:\"a\"`; G int `json:\"a\"` }", "t.A", "same JSON name"},
		{"fold-name", "type A struct{ F int `json:\"a\"`; G int `json:\"A\"` }", "t.A", "equal ignoring case"},
		{"number", "type A struct{ F json.Number }", "t.A", "Number"},
		{"marshal-json", "type A struct{ X int }\nfunc (A) MarshalJSON() ([]byte, error) { return nil, nil }", "t.A", "MarshalJSON"},
		{"unmarshal-json-ptr", "type A struct{ X int }\nfunc (*A) UnmarshalJSON([]byte) error { return nil }", "t.A", "UnmarshalJSON"},
		{"marshal-text", "type K int\nfunc (K) MarshalText() ([]byte, error) { return nil, nil }\ntype A struct{ F K }", "t.A", "MarshalText"},
		{"append-text", "type K string\nfunc (K) AppendText(b []byte) ([]byte, error) { return b, nil }\ntype A struct{ F []K }", "t.A", "AppendText"},
		{"marshal-json-to", "type A struct{ X int }\nfunc (A) MarshalJSONTo() error { return nil }", "t.A", "MarshalJSONTo"},
		{"unexported-type", "type b int\ntype A struct{ F b }", "t.A", "unexported"},
		{"generic", "type G[T any] struct{ X T }\ntype A struct{ F G[int] }", "t.A", "generic"},
		{"unnamed-field-struct", "type A struct{ F struct{ X int } }", "t.A", "unnamed struct"},
		{"unknown-package", "type A struct{ F os.FileMode }", "t.A", "has no alias"},
	}
	for _, c := range cases {
		dir := t.TempDir()
		imp := "import (\n\t\"encoding/json\"\n\t\"os\"\n)\n\nvar _ json.RawMessage\nvar _ os.FileMode\n"
		src := fmt.Sprintf("package t\n\n%s\n%s\n", imp, c.decls)
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
