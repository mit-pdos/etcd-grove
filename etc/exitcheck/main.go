// Command exitcheck lists the process exits in a Go program's own packages:
//
//	exitcheck -C MODDIR -under DIR [-tags TAGS] PATTERN...
//
// It loads PATTERN... in the Go module (or workspace) of MODDIR with `go list -e -export -deps`,
// type-checks every non-test package of that closure whose directory is under DIR (the program's
// own code, not its dependencies), and prints one line per use of a function that ends the
// process or the calling goroutine without a panic (EXITS below), or of a wrapper of one, a call or
// a function value. A wrapper is a function of those packages that calls an exit (or a wrapper) with
// an argument that mentions one of its own parameters (a logger's `Fatal(v ...any)` method), so its
// callers decide what it reports: their calls are listed, as well as its own. An exit whose
// arguments mention none of the parameters (log.Fatal(err) of a failed open) is the function's own
// decision, listed once:
//
//	FILE:LINE:COL<TAB>FUNC<TAB>LINE TEXT, WHITESPACE COLLAPSED
//
// FILE relative to DIR's parent. Used by etc/exit-check.py: under `Robust` (Robustness/) an exit of
// any status is a safe run (Perennial models `syscall.Exit` as `AngelicExit`), so a program that
// reports a violation by exiting is checked by nothing; the checks of a robustness theorem's
// programs must panic. Exits 2 on an error (a package that does not load or type-check).
package main

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
)

// exitFn: a function (Recv "") or method (Recv the receiver's named type, pointer or not) of the
// package Pkg whose name matches Name.
type exitFn struct{ Pkg, Recv, Name string }

// EXITS: what ends the process (os.Exit and the loggers' Fatal, which call it) or the goroutine
// (runtime.Goexit, and testing's FailNow/SkipNow, which call it). Panicking variants (log.Panic,
// zap's Panic/DPanic) are not here: a panic is what a robustness theorem excludes.
var exits = []exitFn{
	{"os", "", `^Exit$`},
	{"syscall", "", `^Exit$`},
	{"runtime", "", `^Goexit$`},
	{"log", "", `^Fatal(f|ln)?$`},
	{"log", "Logger", `^Fatal(f|ln)?$`},
	{"go.uber.org/zap", "Logger", `^Fatal$`},
	{"go.uber.org/zap", "SugaredLogger", `^Fatal(f|w|ln)?$`},
	{"k8s.io/klog", "", `^(Fatal|Exit)(f|ln|Depth)?$`},
	{"k8s.io/klog/v2", "", `^((Fatal|Exit)(f|ln|Depth)?|FlushAndExit)$`},
	{"github.com/golang/glog", "", `^(Fatal|Exit)(f|ln|Depth)?$`},
	{"github.com/sirupsen/logrus", "", `^(Fatal(f|ln)?|Exit)$`},
	{"github.com/sirupsen/logrus", "Logger", `^(Fatal(f|ln)?|Exit)$`},
	{"github.com/sirupsen/logrus", "Entry", `^Fatal(f|ln)?$`},
	{"github.com/rs/zerolog", "Logger", `^Fatal$`},
	{"github.com/rs/zerolog/log", "", `^Fatal$`},
	{"testing", "", `^(Fatal(f)?|FailNow|Skip(f|Now)?)$`}, // methods of T, B, F, common, TB
}

type listed struct {
	ImportPath string
	Dir        string
	GoFiles    []string
	CgoFiles   []string
	Export     string
	Standard   bool
	ImportMap  map[string]string
	Error      *struct{ Err string }
}

type importerFunc func(path string) (*types.Package, error)

func (f importerFunc) Import(path string) (*types.Package, error) { return f(path) }

// wrappers: the functions of the checked packages that forward their parameters to an exit (by
// types.Func.FullName).
var wrappers = map[string]bool{}

func match(obj types.Object) (string, bool) {
	fn, ok := obj.(*types.Func)
	if !ok || fn.Pkg() == nil {
		return "", false
	}
	fn = fn.Origin()
	if wrappers[fn.FullName()] {
		return fn.FullName(), true
	}
	recv := ""
	if sig, ok := fn.Type().(*types.Signature); ok && sig.Recv() != nil {
		t := sig.Recv().Type()
		if p, ok := t.(*types.Pointer); ok {
			t = p.Elem()
		}
		if n, ok := t.(*types.Named); ok {
			recv = n.Obj().Name()
		}
	}
	for _, e := range exits {
		if e.Pkg != fn.Pkg().Path() || !regexp.MustCompile(e.Name).MatchString(fn.Name()) {
			continue
		}
		if e.Pkg != "testing" && e.Recv != recv {
			continue
		}
		return fn.FullName(), true
	}
	return "", false
}

func main() {
	modDir := flag.String("C", ".", "the directory to run go list in (its module or workspace)")
	under := flag.String("under", "", "check only the packages whose directory is under this one")
	tags := flag.String("tags", "", "build tags for go list")
	flag.Parse()
	if *under == "" || flag.NArg() == 0 {
		fmt.Fprintln(os.Stderr, "usage: exitcheck -C MODDIR -under DIR PATTERN...")
		os.Exit(2)
	}
	underAbs, _ := filepath.Abs(*under)
	base := filepath.Dir(underAbs)
	args := []string{"list", "-e", "-export", "-deps", "-json"}
	if *tags != "" {
		args = append(args, "-tags", *tags)
	}
	cmd := exec.Command("go", append(args, flag.Args()...)...)
	cmd.Dir = *modDir
	var out, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &stderr
	if err := cmd.Run(); err != nil {
		fmt.Fprintf(os.Stderr, "%s: go list: %v: %s\n", *modDir, err, stderr.String())
		os.Exit(2)
	}
	var pkgs []*listed
	exports := map[string]string{}
	dec := json.NewDecoder(&out)
	for {
		var p listed
		if err := dec.Decode(&p); err == io.EOF {
			break
		} else if err != nil {
			fmt.Fprintf(os.Stderr, "%s: go list output: %v\n", *modDir, err)
			os.Exit(2)
		}
		if p.Error != nil {
			fmt.Fprintf(os.Stderr, "%s: go list: %s\n", p.ImportPath, p.Error.Err)
			os.Exit(2)
		}
		exports[p.ImportPath] = p.Export
		pkgs = append(pkgs, &p)
	}
	fset := token.NewFileSet()
	gc := importer.ForCompiler(fset, "gc", func(path string) (io.ReadCloser, error) {
		e, ok := exports[path]
		if !ok || e == "" {
			return nil, fmt.Errorf("no export data for %s", path)
		}
		return os.Open(e)
	})
	var lines []string
	checked := 0
	for _, p := range pkgs {
		d, _ := filepath.Abs(p.Dir)
		if p.Standard || !(d == underAbs || strings.HasPrefix(d, underAbs+string(filepath.Separator))) {
			continue
		}
		checked++
		var files []*ast.File
		for _, f := range append(append([]string{}, p.GoFiles...), p.CgoFiles...) {
			af, err := parser.ParseFile(fset, filepath.Join(p.Dir, f), nil, parser.SkipObjectResolution)
			if err != nil {
				fmt.Fprintln(os.Stderr, err)
				os.Exit(2)
			}
			files = append(files, af)
		}
		info := &types.Info{Uses: map[*ast.Ident]types.Object{}, Defs: map[*ast.Ident]types.Object{}}
		im := p.ImportMap
		conf := types.Config{FakeImportC: len(p.CgoFiles) > 0, Importer: importerFunc(func(path string) (*types.Package, error) {
			if m, ok := im[path]; ok {
				path = m
			}
			return gc.Import(path)
		})}
		if _, err := conf.Check(p.ImportPath, fset, files, info); err != nil {
			fmt.Fprintf(os.Stderr, "%s: type-checking: %v\n", p.ImportPath, err)
			os.Exit(2)
		}
		// the package's own wrappers, to a fixpoint (go list -deps lists a package after its
		// dependencies, so their wrappers are known)
		for changed := true; changed; {
			changed = false
			for _, f := range files {
				for _, d := range f.Decls {
					fd, ok := d.(*ast.FuncDecl)
					if !ok || fd.Body == nil {
						continue
					}
					obj, _ := info.Defs[fd.Name].(*types.Func)
					if obj == nil || wrappers[obj.FullName()] {
						continue
					}
					if forwards(fd, info) {
						wrappers[obj.FullName()] = true
						changed = true
					}
				}
			}
		}
		for id, obj := range info.Uses {
			name, ok := match(obj)
			if !ok {
				continue
			}
			pos := fset.Position(id.Pos())
			rel, _ := filepath.Rel(base, pos.Filename)
			src, _ := os.ReadFile(pos.Filename)
			text := ""
			if ls := strings.Split(string(src), "\n"); pos.Line-1 < len(ls) {
				text = strings.Join(strings.Fields(ls[pos.Line-1]), " ")
			}
			lines = append(lines, fmt.Sprintf("%s:%d:%d\t%s\t%s", rel, pos.Line, pos.Column, name, text))
		}
	}
	sort.Strings(lines)
	for _, l := range lines {
		fmt.Println(l)
	}
	fmt.Fprintf(os.Stderr, "exitcheck: %d packages checked\n", checked)
}

// forwards: fd's body (its closures included) calls an exit or a wrapper with an argument that
// mentions one of fd's parameters.
func forwards(fd *ast.FuncDecl, info *types.Info) bool {
	params := map[types.Object]bool{}
	for _, fl := range fd.Type.Params.List {
		for _, n := range fl.Names {
			if o := info.Defs[n]; o != nil {
				params[o] = true
			}
		}
	}
	found := false
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || found {
			return !found
		}
		var id *ast.Ident
		switch f := ast.Unparen(call.Fun).(type) {
		case *ast.Ident:
			id = f
		case *ast.SelectorExpr:
			id = f.Sel
		}
		if id == nil {
			return true
		}
		if _, ok := match(info.Uses[id]); !ok {
			return true
		}
		for _, a := range call.Args {
			ast.Inspect(a, func(m ast.Node) bool {
				if x, ok := m.(*ast.Ident); ok && params[info.Uses[x]] {
					found = true
				}
				return !found
			})
		}
		return !found
	})
	return found
}
