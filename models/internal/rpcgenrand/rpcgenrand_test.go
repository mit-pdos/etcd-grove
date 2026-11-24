// Package rpcgenrand is the differential test of the net/rpc model's codec generator
// (models/net/rpc/rpcgen.py) over random Go types: each run writes a Go module with random named
// types (structs of every accepted field kind, nested, through pointers, slices and maps; named
// basic, slice and map types; unexported fields) and a receiver whose methods take them, runs
// rpcgen on it (its dump by reflection included), and runs the generated regression test, which
// checks the codec against real encoding/gob (decoding into zero and into random non-zero values)
// and the receiver's methods against net/rpc's suitableMethods. TestRefusals checks one input per
// construct outside the subset is refused, naming it.
//
// RPCGEN_RAND_TYPES (default 6) modules per run, RPCGEN_RAND_SEED (default 1) the first seed,
// RPCGEN_TEST_SCALE the generated tests' scale.
package rpcgenrand

import (
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

type setup struct {
	rpcgen, modRoot string
}

func newSetup(t *testing.T) setup {
	wd, err := os.Getwd()
	must(t, err)
	modRoot := filepath.Clean(filepath.Join(wd, "..", ".."))
	gen := filepath.Join(modRoot, "net", "rpc", "rpcgen.py")
	if _, err := os.Stat(gen); err != nil {
		t.Skipf("no rpcgen.py: %v", err)
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

func runCode(dir string, name string, args ...string) (string, int) {
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "GOWORK=off", "GOPROXY=off", "GOFLAGS=-mod=mod")
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

// module writes a Go module rpcgenrand.tmp into dir (importing models.lab) with package t
// holding src, and the [rpc] input naming receivers and types.
func (s setup) module(t *testing.T, dir, src string, receivers, types []string) {
	t.Helper()
	gomod := fmt.Sprintf("module rpcgenrand.tmp\n\ngo 1.27\n\nrequire models.lab v0.0.0-00010101000000-000000000000\n\n"+
		"replace models.lab => %s\n", s.modRoot)
	must(t, os.WriteFile(filepath.Join(dir, "go.mod"), []byte(gomod), 0o644))
	sum, err := os.ReadFile(filepath.Join(s.modRoot, "go.sum"))
	must(t, err)
	must(t, os.WriteFile(filepath.Join(dir, "go.sum"), sum, 0o644))
	must(t, os.MkdirAll(filepath.Join(dir, "t"), 0o755))
	must(t, os.WriteFile(filepath.Join(dir, "t", "t.go"), []byte(src), 0o644))
	q := func(xs []string) string {
		var o []string
		for _, x := range xs {
			o = append(o, strconv.Quote(x))
		}
		return "[" + strings.Join(o, ", ") + "]"
	}
	toml := fmt.Sprintf("[rpc]\nimports = { t = \"rpcgenrand.tmp/t\" }\nreceivers = %s\ntypes = %s\n", q(receivers), q(types))
	must(t, os.WriteFile(filepath.Join(dir, "rpc.toml"), []byte(toml), 0o644))
}

// gen writes random type declarations.
type gen struct {
	r     *rand.Rand
	decls []string
	n     int
	depth int
}

var basics = []string{"bool", "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16",
	"uint32", "uint64", "string"}

// fieldNames include names the generated code also uses as identifiers.
var fieldNames = []string{"A", "B", "P", "R", "V", "X", "Y", "Ok", "N", "Tag", "Data", "String", "Error", "Len"}

func (g *gen) name() string {
	g.n++
	return fmt.Sprintf("T%d", g.n)
}

// typ returns a type expression; field: a pointer is allowed at the top.
func (g *gen) typ(depth int, field bool) string {
	if field && g.r.Intn(6) == 0 {
		return "*" + g.typ(depth, false)
	}
	k := g.r.Intn(10)
	if depth > 2 {
		k = g.r.Intn(3)
	}
	switch k {
	case 0, 1:
		return basics[g.r.Intn(len(basics))]
	case 2:
		if g.r.Intn(2) == 0 {
			return "[]byte"
		}
		n := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s %s", n, basics[g.r.Intn(len(basics))]))
		return n
	case 3:
		return "[]" + g.typ(depth+1, false)
	case 4:
		return "map[" + g.key() + "]" + g.typ(depth+1, false)
	case 5:
		n := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s []%s", n, g.typ(depth+1, false)))
		return n
	case 6:
		n := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s map[%s]%s", n, g.key(), g.typ(depth+1, false)))
		return n
	default:
		return g.strct(depth + 1)
	}
}

func (g *gen) key() string {
	switch g.r.Intn(3) {
	case 0:
		return "string"
	case 1:
		n := g.name()
		g.decls = append(g.decls, fmt.Sprintf("type %s %s", n, basics[g.r.Intn(len(basics))]))
		return n
	}
	return basics[g.r.Intn(len(basics))]
}

func (g *gen) strct(depth int) string {
	n := g.name()
	var fs []string
	used := map[string]bool{}
	nf := g.r.Intn(6)
	for i := 0; i < nf; i++ {
		f := fieldNames[g.r.Intn(len(fieldNames))]
		if used[f] {
			continue
		}
		used[f] = true
		fs = append(fs, fmt.Sprintf("\t%s %s", f, g.typ(depth, true)))
	}
	if len(fs) > 0 && g.r.Intn(3) == 0 {
		fs = append(fs, "\thidden int")
	}
	g.decls = append(g.decls, fmt.Sprintf("type %s struct {\n%s\n}", n, strings.Join(fs, "\n")))
	return n
}

// source returns a package t with random types and a receiver Svc whose methods take them.
func source(seed int64) (string, []string) {
	g := &gen{r: rand.New(rand.NewSource(seed))}
	var methods []string
	var extra []string
	for i := 0; i < 1+g.r.Intn(5); i++ {
		a := g.typ(0, false)
		r := g.typ(0, false)
		ap := a
		if g.r.Intn(3) != 0 {
			ap = "*" + a
		}
		methods = append(methods, fmt.Sprintf("func (s *Svc) M%d(a %s, r *%s) error { return nil }", i, ap, r))
	}
	extra = append(extra, "t."+g.strct(0))
	src := "package t\n\n// Svc is the receiver.\ntype Svc struct{}\n\n" + strings.Join(g.decls, "\n\n") + "\n\n" +
		strings.Join(methods, "\n\n") + "\n"
	return src, extra
}

func TestRandomTypes(t *testing.T) {
	s := newSetup(t)
	n, _ := strconv.Atoi(os.Getenv("RPCGEN_RAND_TYPES"))
	if n <= 0 {
		n = 6
	}
	seed0, _ := strconv.ParseInt(os.Getenv("RPCGEN_RAND_SEED"), 10, 64)
	if seed0 == 0 {
		seed0 = 1
	}
	for i := 0; i < n; i++ {
		seed := seed0 + int64(i)
		src, extra := source(seed)
		dir := t.TempDir()
		s.module(t, dir, src, []string{"*t.Svc"}, extra)
		out, code := runCode(dir, "python3", s.rpcgen, "rpc.toml", "codec", "--pkg", "codec")
		if code != 0 {
			t.Fatalf("seed %d: rpcgen: exit %d\n%s\n%s", seed, code, out, src)
		}
		out, code = runCode(dir, "go", "test", "-count=1", "./codec")
		if code != 0 {
			t.Fatalf("seed %d: the generated test failed:\n%s\n%s", seed, out, src)
		}
	}
}

// The receiver in a package other than its methods' types' (gryff: *masterlib.Master taking
// masterproto's): rpc_gen.go (the codec) uses only the types, so it must not import the receiver's
// package (an unused import does not compile); the generated test, which checks the receiver, does.
func TestReceiverOtherPackage(t *testing.T) {
	s := newSetup(t)
	dir := t.TempDir()
	s.module(t, dir, "package t\n\ntype A struct{ X int }\n\ntype R struct{ Ok bool }\n", nil, nil)
	must(t, os.MkdirAll(filepath.Join(dir, "srv"), 0o755))
	must(t, os.WriteFile(filepath.Join(dir, "srv", "srv.go"), []byte("package srv\n\nimport \"rpcgenrand.tmp/t\"\n\n"+
		"type Svc struct{}\n\nfunc (s *Svc) M(a *t.A, r *t.R) error { return nil }\n"), 0o644))
	toml := "[rpc]\nimports = { t = \"rpcgenrand.tmp/t\", srv = \"rpcgenrand.tmp/srv\" }\nreceivers = [\"*srv.Svc\"]\n"
	must(t, os.WriteFile(filepath.Join(dir, "rpc.toml"), []byte(toml), 0o644))
	out, code := runCode(dir, "python3", s.rpcgen, "rpc.toml", "codec", "--pkg", "codec")
	if code != 0 {
		t.Fatalf("rpcgen: exit %d\n%s", code, out)
	}
	out, code = runCode(dir, "go", "test", "-count=1", "./codec")
	if code != 0 {
		t.Fatalf("the generated package or its test failed:\n%s", out)
	}
}

// One input per construct outside the subset: refused (exit 2), naming it.
func TestRefusals(t *testing.T) {
	s := newSetup(t)
	cases := []struct{ name, decls, arg, want string }{
		{"float", "type A struct{ F float64 }", "*t.A", "kind float64"},
		{"complex", "type A struct{ F complex128 }", "*t.A", "kind complex128"},
		{"interface", "type A struct{ F any }", "*t.A", "kind interface"},
		{"array", "type A struct{ F [2]int }", "*t.A", "kind array"},
		{"chan", "type A struct{ F chan int }", "*t.A", "kind chan"},
		{"func", "type A struct{ F func() }", "*t.A", "kind func"},
		{"uintptr", "type A struct{ F uintptr }", "*t.A", "kind uintptr"},
		{"embedded", "type E struct{ X int }\ntype A struct{ E }", "*t.A", "embedded"},
		{"no-exported", "type A struct{ x int }", "*t.A", "none exported"},
		{"recursive", "type A struct{ Next *A }", "*t.A", "recursive"},
		{"ptr-elem", "type A struct{ F []*int }", "*t.A", "a pointer here"},
		{"ptr-ptr", "type A struct{ F **int }", "*t.A", "a pointer here"},
		{"unnamed-struct", "type A struct{ F struct{ X int } }", "*t.A", "unnamed struct"},
		{"unexported-type", "type b int\ntype A struct{ F b }", "*t.A", "unexported"},
		{"generic", "type G[T any] struct{ X T }\ntype A struct{ F G[int] }", "*t.A", "generic"},
		{"gob-encoder", "type A struct{ X int }\nfunc (A) GobEncode() ([]byte, error) { return nil, nil }", "*t.A", "gob_encoder"},
		{"text-marshaler", "type A struct{ X int }\nfunc (*A) MarshalText() ([]byte, error) { return nil, nil }", "*t.A", "text_marshaler"},
		{"arg-ptr-ptr", "type A struct{ X int }", "**t.A", "a pointer to a pointer"},
	}
	for _, c := range cases {
		dir := t.TempDir()
		arg := strings.TrimPrefix(strings.Replace(c.arg, "t.", "", 1), "")
		src := fmt.Sprintf("package t\n\ntype Svc struct{}\n\n%s\n\nfunc (s *Svc) M(a %s, r *int) error { return nil }\n", c.decls, arg)
		s.module(t, dir, src, []string{"*t.Svc"}, nil)
		out, code := runCode(dir, "python3", s.rpcgen, "rpc.toml", "codec", "--pkg", "codec")
		if code != 2 || !strings.Contains(out, c.want) {
			t.Errorf("%s: rpcgen exit %d, want 2 naming %q:\n%s", c.name, code, c.want, out)
		}
		if _, err := os.Stat(filepath.Join(dir, "codec")); err == nil {
			t.Errorf("%s: a refused input wrote files", c.name)
		}
	}
}
