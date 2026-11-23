package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// run writes ORIG and PATCHED versions of a package's files (the same names) into a module each
// (module m, package m/p) and checks them; it returns prophcheck's errors.
func run(t *testing.T, orig, patched map[string]string) []string {
	t.Helper()
	// not t.TempDir(): its name holds the test's, which the errors' positions would show
	dir, err := os.MkdirTemp("", "prophcheck")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { os.RemoveAll(dir) })
	write := func(root string, files map[string]string) {
		if err := os.MkdirAll(filepath.Join(root, "p"), 0o755); err != nil {
			t.Fatal(err)
		}
		gomod := "module m\n\ngo 1.27\n"
		if err := os.WriteFile(filepath.Join(root, "go.mod"), []byte(gomod), 0o644); err != nil {
			t.Fatal(err)
		}
		// a stand-in for github.com/goose-lang/primitive (the module's own package: the field
		// check type-checks without the network)
		prim := filepath.Join(root, "primitive")
		if err := os.MkdirAll(prim, 0o755); err != nil {
			t.Fatal(err)
		}
		src := "package primitive\n\ntype prophId struct{ x int }\n\ntype ProphId = *prophId\n\n" +
			"func NewProph() ProphId { return &prophId{} }\n\n" +
			"func (p *prophId) ResolveBool(b bool) {}\n\nfunc (p *prophId) ResolveU64(x uint64) {}\n\n" +
			"func (p *prophId) Resolve(v any) {}\n"
		if err := os.WriteFile(filepath.Join(prim, "proph.go"), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
		for name, s := range files {
			if err := os.WriteFile(filepath.Join(root, "p", name), []byte(s), 0o644); err != nil {
				t.Fatal(err)
			}
		}
	}
	write(filepath.Join(dir, "orig"), orig)
	write(filepath.Join(dir, "patched"), patched)
	var pairs [][2]string
	for name := range patched {
		pairs = append(pairs, [2]string{filepath.Join(dir, "orig", "p", name),
			filepath.Join(dir, "patched", "p", name)})
	}
	return check(pairs)
}

// the test files import the stand-in as "github.com/goose-lang/primitive" through this replace:
// the stand-in module's path is m, so the files import "m/primitive" under the name primitive;
// prophcheck recognizes the import by path, so the tests that need the import erased use
// primImport (the real path) and do not type-check.
const primImport = `import "github.com/goose-lang/primitive"`

func wantOK(t *testing.T, errs []string) {
	t.Helper()
	if len(errs) > 0 {
		t.Fatalf("want no errors, got:\n%s", strings.Join(errs, "\n"))
	}
}

func wantErr(t *testing.T, errs []string, sub string) {
	t.Helper()
	for _, e := range errs {
		if strings.Contains(e, sub) {
			t.Logf("%s", e)
			return
		}
	}
	t.Fatalf("want an error containing %q, got:\n%s", sub, strings.Join(errs, "\n"))
}

const origKV = `package p

type KV struct {
	m map[string]string
	n int
}

func (kv *KV) Get(k string) string {
	v := kv.m[k]
	return v
}
`

// The first rule's patch: a local prophecy resolved with a read-only expression.
func TestLocalProphecy(t *testing.T) {
	patched := `package p

` + primImport + `

type KV struct {
	m map[string]string
	n int
}

func (kv *KV) Get(k string) string {
	pr := primitive.NewProph()
	v := kv.m[k]
	pr.ResolveBool(len(v) == 0)
	if kv.n > 0 {
		pr.ResolveU64(uint64(kv.n))
	} else {
		pr.ResolveU64(0)
	}
	return v
}
`
	wantOK(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": patched}))
}

// A prophecy-only variable, prophecy-only helpers (a method calling a function, a loop, locals, an if, `&` of a
// field) and their calls at statement level and in an if on a read-only condition.
func TestProphOnlyVariableAndHelpers(t *testing.T) {
	patched := `package p

` + primImport + `

type KV struct {
	m map[string]string
	n int
}

var trace = primitive.NewProph()

func resolveLen(s string, n *int) {
	trace.ResolveU64(uint64(len(s)))
	for i := 0; i < len(s); i++ {
		b := s[i]
		trace.ResolveU64(uint64(b))
	}
	if *n > 0 {
		trace.ResolveBool(true)
	}
}

func (kv *KV) resolveGet(k string) {
	trace.ResolveU64(1)
	x := 2
	x += kv.n
	x++
	trace.ResolveU64(uint64(x))
	resolveLen(k, &kv.n)
}

func (kv *KV) Get(k string) string {
	kv.resolveGet(k)
	v := kv.m[k]
	if v != "" {
		resolveLen(v, &kv.n)
	}
	return v
}
`
	wantOK(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": patched}))
}

// Helpers in one file, called from another file of the package.
func TestHelpersAcrossFiles(t *testing.T) {
	orig2 := "package p\n\nfunc Use(kv *KV) string {\n\treturn kv.Get(\"a\")\n}\n"
	patched1 := `package p

` + primImport + `

type KV struct {
	m map[string]string
	n int
}

var trace = primitive.NewProph()

func (kv *KV) resolveN() {
	trace.ResolveU64(uint64(kv.n))
}

func (kv *KV) Get(k string) string {
	v := kv.m[k]
	return v
}
`
	patched2 := "package p\n\nfunc Use(kv *KV) string {\n\tkv.resolveN()\n\treturn kv.Get(\"a\")\n}\n"
	wantOK(t, run(t, map[string]string{"kv.go": origKV, "use.go": orig2},
		map[string]string{"kv.go": patched1, "use.go": patched2}))
}

// Negative: what a helper may not do.
func TestHelperRefusals(t *testing.T) {
	cases := []struct{ name, helper, call, want string }{
		{"writes the heap", "func (kv *KV) g() {\n\tkv.n = 1\n}\n", "kv.g()",
			"assigns to something other than its own locals"},
		{"calls a non-helper", "func (kv *KV) g() {\n\tkv.Get(\"x\")\n}\n", "kv.g()",
			"neither a resolution nor a prophecy-only helper's call"},
		{"returns a value", "func (kv *KV) g() int {\n\treturn 1\n}\n", "kv.g()", "has results"},
		{"recurses", "func (kv *KV) g() {\n\tkv.h()\n}\n\nfunc (kv *KV) h() {\n\tkv.g()\n}\n",
			"kv.g()", "can call itself"},
		{"loops with <=", "func g(n int) {\n\tfor i := 0; i <= n; i++ {\n\t}\n}\n", "g(1)",
			"loop not of the form"},
		{"loops forever", "func g() {\n\tfor {\n\t}\n}\n", "g()", "loop not of the form"},
		{"assigns its counter", "func g(n int) {\n\tfor i := 0; i < n; i++ {\n\t\ti = 0\n\t}\n}\n",
			"g(1)", "assigns to i, not one of its own locals"},
		{"ranges", "func g(s []int) {\n\tfor range s {\n\t}\n}\n", "g(nil)", "not allowed"},
		{"starts a goroutine", "func g() {\n\tgo g()\n}\n", "g()", "not allowed"},
		{"defines with a call", "func (kv *KV) g() {\n\tx := kv.Get(\"y\")\n\t_ = x\n}\n", "kv.g()",
			"not a read-only expression"},
		{"is an exported method", "func (kv *KV) String() {\n}\n", "kv.String()", "is exported"},
		{"receives from a channel", "func g(c chan int) {\n\tx := <-c\n\t_ = x\n}\n", "g(nil)",
			"not a read-only expression"},
		{"is called with a call", "func g(n int) {\n}\n", "g(len(kv.Get(\"a\")))",
			"an argument is not read-only"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			patched := strings.Replace(origKV, "\tv := kv.m[k]\n", "\t"+tc.call+"\n\tv := kv.m[k]\n", 1) +
				"\n" + tc.helper
			wantErr(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": patched}), tc.want)
		})
	}
}

// Negative: declarations a patch may not add, and code that is not prophecy-only code.
func TestDeclarationRefusals(t *testing.T) {
	cases := []struct{ name, patched, want string }{
		{"a constant", origKV + "\nconst evGet uint64 = 1\n", "adds the constant evGet"},
		{"a type", origKV + "\ntype extra struct{}\n", "adds the type extra"},
		{"a variable not from NewProph", origKV + "\nvar trace = 3\n",
			"`var NAME = primitive.NewProph()`"},
		{"an init", strings.Replace(origKV, "package p\n", "package p\n\n"+primImport+"\n", 1) +
			"\nvar trace = primitive.NewProph()\n\nfunc init() {\n\ttrace.ResolveU64(1)\n}\n",
			"with its prophecy-only code erased, it is not"},
		{"a field of another type", strings.Replace(origKV, "\tn int\n", "\tn int\n\tg int\n", 1),
			"`NAME primitive.ProphId`"},
		{"an exported field", strings.Replace(
			strings.Replace(origKV, "package p\n", "package p\n\n"+primImport+"\n", 1),
			"\tn int\n", "\tn int\n\tG primitive.ProphId\n", 1), "is exported"},
		{"a changed statement", strings.Replace(origKV, "v := kv.m[k]", "v := kv.m[k+\"\"]", 1),
			"with its prophecy-only code erased, it is not"},
		{"an added statement", strings.Replace(origKV, "\tv := kv.m[k]\n", "\tkv.n++\n\tv := kv.m[k]\n", 1),
			"with its prophecy-only code erased, it is not"},
		{"an added assignment",
			strings.Replace(origKV, "\tv := kv.m[k]\n", "\tv := kv.m[k]\n\t_ = kv.n\n", 1),
			"with its prophecy-only code erased, it is not"},
		{"a helper named like an original identifier", origKV + "\nfunc m() {\n}\n",
			"with its prophecy-only code erased, it is not"},
		{"a resolution of an undeclared prophecy",
			strings.Replace(origKV, "\tv := kv.m[k]\n", "\tq.ResolveU64(1)\n\tv := kv.m[k]\n", 1),
			"which the patch has not declared before"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			wantErr(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": tc.patched}), tc.want)
		})
	}
}

// Prophecy-only fields: the program's uses of the struct are type-checked, so these files import the
// test module's stand-in for primitive under its real name `primitive` (prophcheck recognizes the
// import of github.com/goose-lang/primitive by path; these files keep their import and the
// original has it too).
const origField = `package p

import primitive "m/primitive"

var _ primitive.ProphId

type R struct {
	n int
}

func New(n int) *R {
	return &R{n: n}
}

func (r *R) Step() {
	r.n++
}
`

func fieldPatched(extra string) string {
	s := strings.Replace(origField, "\tn int\n}", "\tn int\n\tpr primitive.ProphId\n}", 1)
	s = strings.Replace(s, "&R{n: n}", "&R{n: n, pr: primitive.NewProph()}", 1)
	s = strings.Replace(s, "\tr.n++\n", "\tr.pr.ResolveU64(uint64(r.n))\n\tr.n++\n", 1)
	return s + extra
}

func TestProphOnlyField(t *testing.T) {
	extra := `
func (r *R) reset() {
	r.pr.ResolveBool(r.n == 0)
}

func Reset(r *R) {
	r.pr = primitive.NewProph()
	r.reset()
}
`
	orig := origField + "\nfunc Reset(r *R) {\n}\n"
	wantOK(t, run(t, map[string]string{"r.go": orig}, map[string]string{"r.go": fieldPatched(extra)}))
}

func TestProphOnlyFieldRefusals(t *testing.T) {
	cases := []struct{ name, use, want string }{
		{"compared", "func Same(a, b R) bool {\n\treturn a == b\n}\n", "compares a struct with a prophecy-only field"},
		{"compared in an array", "func Same(a, b [2]R) bool {\n\treturn a != b\n}\n",
			"compares a struct with a prophecy-only field"},
		{"a map key", "var seen map[R]bool\n", "a map type whose key contains"},
		{"a map key in a struct", "type S struct {\n\tm map[[1]R]int\n}\n", "a map type whose key contains"},
		{"converted to any", "func Show(r *R) any {\n\treturn r\n}\n", "to an interface"},
		{"passed as any", "func sink(x any) {}\n\nfunc Show(r R) {\n\tsink(r)\n}\n", "to an interface"},
		{"in a slice of any", "func Show(r *R) []any {\n\treturn []any{r}\n}\n", "to an interface"},
		{"switched on", "func Sw(a, b R) {\n\tswitch a {\n\tcase b:\n\t}\n}\n", "switch"},
		{"a type argument", "func id[T any](x T) T {\n\treturn x\n}\n\nfunc Use(r R) R {\n\treturn id(r)\n}\n",
			"instantiates id"},
		{"unsafe.Sizeof", "func Size(r R) uintptr {\n\treturn unsafe.Sizeof(r)\n}\n", "unsafe.Sizeof"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			use := tc.use
			orig, patched := origField+"\n"+use, fieldPatched("\n"+use)
			if strings.Contains(use, "unsafe.") {
				orig = strings.Replace(orig, "import primitive \"m/primitive\"\n",
					"import (\n\tprimitive \"m/primitive\"\n\t\"unsafe\"\n)\n", 1)
				patched = strings.Replace(patched, "import primitive \"m/primitive\"\n",
					"import (\n\tprimitive \"m/primitive\"\n\t\"unsafe\"\n)\n", 1)
			}
			wantErr(t, run(t, map[string]string{"r.go": orig}, map[string]string{"r.go": patched}), tc.want)
		})
	}
}

// The original program's own uses of a struct without prophecy-only fields are not refused.
func TestFieldUsesOnlyProphOnlyFieldStructs(t *testing.T) {
	orig := origField + "\ntype Q struct{ a int }\n\nvar seen map[Q]bool\n\nfunc Show(q Q) any {\n\treturn q == q\n}\n"
	patched := fieldPatched("\ntype Q struct{ a int }\n\nvar seen map[Q]bool\n\nfunc Show(q Q) any {\n\treturn q == q\n}\n")
	wantOK(t, run(t, map[string]string{"r.go": orig}, map[string]string{"r.go": patched}))
}

// An original `if` without statements is not prophecy-only code (it stays, and the files match).
func TestEmptyIfIsNotProphOnly(t *testing.T) {
	orig := strings.Replace(origKV, "\tv := kv.m[k]\n", "\tif kv.n > 0 {\n\t}\n\tv := kv.m[k]\n", 1)
	patched := strings.Replace(orig, "package p\n", "package p\n\n"+primImport+"\n", 1)
	patched = strings.Replace(patched, "\tv := kv.m[k]\n", "\tpr := primitive.NewProph()\n\tpr.ResolveU64(1)\n\tv := kv.m[k]\n", 1)
	wantOK(t, run(t, map[string]string{"kv.go": orig}, map[string]string{"kv.go": patched}))
}

// A prophecy-only variable initialized by a prophecy-only initializer (the form Goose translates).
func TestProphOnlyInitializer(t *testing.T) {
	patched := strings.Replace(origKV, "package p\n", "package p\n\n"+primImport+"\n", 1) + `
var trace primitive.ProphId

func init() {
	p := primitive.NewProph()
	trace = p
}

func (kv *KV) resolveN() {
	trace.ResolveU64(uint64(kv.n))
}
`
	patched = strings.Replace(patched, "\tv := kv.m[k]\n", "\tkv.resolveN()\n\tv := kv.m[k]\n", 1)
	wantOK(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": patched}))
}

func TestProphOnlyInitializerRefusals(t *testing.T) {
	head := strings.Replace(origKV, "package p\n", "package p\n\n"+primImport+"\n", 1)
	cases := []struct{ name, extra, want string }{
		{"no initializer", "\nvar trace primitive.ProphId\n", "with a prophecy-only initializer"},
		{"an initializer that does more",
			"\nvar trace primitive.ProphId\n\nfunc init() {\n\tp := primitive.NewProph()\n\ttrace = p\n\tp.ResolveU64(1)\n}\n",
			"with a prophecy-only initializer"},
		{"an initializer of an original variable",
			"\nvar trace = primitive.NewProph()\n\nvar g int\n\nfunc init() {\n\tg = 1\n}\n",
			"with its prophecy-only code erased, it is not"},
		{"two initializers",
			"\nvar trace primitive.ProphId\n\nfunc init() {\n\ttrace = primitive.NewProph()\n}\n\nfunc init() {\n\ttrace = primitive.NewProph()\n}\n",
			"has two initializers"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			wantErr(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": head + tc.extra}), tc.want)
		})
	}
}

// Resolve(any): one value per resolution, a struct literal (a struct type of the package or a
// struct type literal) or a conversion to any of read-only values, in a helper (from its locals)
// and at statement level.
func TestResolveAny(t *testing.T) {
	patched := `package p

` + primImport + `

type KV struct {
	m map[string]string
	n int
}

var trace = primitive.NewProph()

func (kv *KV) resolveGet(k string, v string) {
	s := ""
	for i := 0; i < len(k); i++ {
		s += k[i : i+1]
	}
	trace.Resolve(struct {
		tag uint64
		key string
		val string
		in  struct{ n int }
	}{1, s, v, struct{ n int }{kv.n}})
	trace.Resolve(any(kv.n))
	trace.Resolve(interface{}(uint64(len(v))))
	trace.Resolve(KV{m: kv.m, n: kv.n})
	trace.Resolve(k)
}

func (kv *KV) Get(k string) string {
	pr := primitive.NewProph()
	v := kv.m[k]
	pr.Resolve(struct{ k, v string }{k: k, v: v})
	kv.resolveGet(k, v)
	return v
}
`
	wantOK(t, run(t, map[string]string{"kv.go": origKV}, map[string]string{"kv.go": patched}))
}

// Negative: a Resolve argument that allocates, calls, or is not one value.
func TestResolveAnyRefusals(t *testing.T) {
	const want = "its argument is not one resolved value"
	orig := origKV + "\ntype L []int\n"
	cases := []struct{ name, arg string }{
		{"a pointer to a literal", "&KV{n: 1}"},
		{"a slice literal", "[]int{kv.n}"},
		{"a map literal", "map[int]int{1: kv.n}"},
		{"an array literal", "[1]int{kv.n}"},
		{"a literal of a non-struct type", "L{kv.n}"},
		{"a literal of another package's type", "q.T{N: kv.n}"},
		{"make", "make([]int, kv.n)"},
		{"new", "new(int)"},
		{"append", "append(L(nil), kv.n)"},
		{"a call in a struct literal", "struct{ s string }{kv.Get(\"a\")}"},
		{"a call converted to any", "any(kv.Get(\"a\"))"},
		{"a closure", "func() {}"},
		{"two arguments", "kv.n, kv.n"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			patched := strings.Replace(orig, "\tv := kv.m[k]\n",
				"\tpr := primitive.NewProph()\n\tpr.Resolve("+tc.arg+")\n\tv := kv.m[k]\n", 1)
			patched = strings.Replace(patched, "package p\n", "package p\n\n"+primImport+"\n", 1)
			wantErr(t, run(t, map[string]string{"kv.go": orig}, map[string]string{"kv.go": patched}), want)
		})
	}
	// in a helper too
	patched := strings.Replace(orig, "\tv := kv.m[k]\n", "\tkv.g()\n\tv := kv.m[k]\n", 1) +
		"\nfunc (kv *KV) g() {\n\ttrace.Resolve(&KV{n: kv.n})\n}\n"
	patched = strings.Replace(patched, "package p\n", "package p\n\n"+primImport+"\n\nvar trace = primitive.NewProph()\n", 1)
	wantErr(t, run(t, map[string]string{"kv.go": orig}, map[string]string{"kv.go": patched}), want)
}
