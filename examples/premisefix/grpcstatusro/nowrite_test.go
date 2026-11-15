package grpcstatusro

// The static half of E1's evidence: no code linked into etcd (its client, its gRPC server, its
// cache) or into the Kubernetes etcd3 storage writes a grpc *Status after it is built, nor the
// *spb.Status inside one, nor the *Status field of a *status.Error.
//
// Status's only field, s *spb.Status, is unexported, so only package internal/status can name it;
// any other package can write a Status only as a whole struct (*p = *q, an assignment of type
// Status) or through unsafe. The scan type-checks, from source, every non-standard package of the
// closures below that depends on internal/status (a package that does not cannot hold a *Status
// statically), and reports:
//
//   - an assignment, ++/--, range assignment or & whose target contains a selection of the field
//     s of Status or of Error (s.s = ..., s.s.Code = ..., *s.s = ..., e.s = ..., &s.s);
//   - an assignment whose target has type Status or Error itself (*p = *q), or a & of an existing
//     Status/Error (not a composite literal);
//   - an unsafe.Pointer conversion of a *Status/*Error;
//   - a read of the field s outside internal/status, or in internal/status outside the functions
//     listed in statusFieldReaders (each of which only reads: Code/Message read s.s.Code/Message,
//     Proto and Is pass s.s to proto.Clone/proto.Equal, Details reads s.s.Details and unmarshals
//     each Any into a new message, RawStatusProto returns s.s; Error's Error, GRPCStatus and Is
//     read e.s);
//   - a call of internal/status.RawStatusProto (the only way out of the package to the *spb.Status)
//     outside internal/transport's server, or one whose result is used other than as
//     p.GetDetails(), proto.Marshal(p) or pretty.ToJSON(p) (reads; Marshal's size cache is an
//     atomic cache inside the message, not its code or message).
//
// Not covered: a generic function writing through a *T instantiated with Status (the type checker
// sees T), and reflection; the race tests of grpcstatusro_test.go observe the running code instead.

import (
	"bytes"
	"encoding/json"
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
	"sort"
	"strings"
	"testing"
)

const statusPath = "google.golang.org/grpc/internal/status"

// The functions of internal/status that read the field s of a Status (keyed "Recv.Name" for
// methods). Construction (Status{s: ...}) is a composite literal, not a selection.
var statusFieldReaders = map[string]bool{
	"Status.Code": true, "Status.Message": true, "Status.Proto": true, "Status.Details": true,
	"Error.Is": true, "RawStatusProto": true,
	// The field s of an Error (a *Status):
	"Error.Error": true, "Error.GRPCStatus": true,
}

type listPkg struct {
	ImportPath string
	Dir        string
	Export     string
	GoFiles    []string
	CgoFiles   []string
	Standard   bool
	Deps       []string
	Module     *struct{ Path string }
}

func goList(t *testing.T, dir string, patterns ...string) []listPkg {
	t.Helper()
	args := append([]string{"list", "-deps", "-export",
		"-json=ImportPath,Dir,Export,GoFiles,CgoFiles,Standard,Deps,Module"}, patterns...)
	cmd := exec.Command("go", args...)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "GOWORK=off")
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil {
		t.Fatalf("go list in %s: %v\n%s", dir, err, stderr.String())
	}
	var pkgs []listPkg
	dec := json.NewDecoder(bytes.NewReader(out))
	for {
		var p listPkg
		if err := dec.Decode(&p); err == io.EOF {
			break
		} else if err != nil {
			t.Fatal(err)
		}
		pkgs = append(pkgs, p)
	}
	return pkgs
}

func isTargetNamed(ty types.Type) (string, bool) {
	n, ok := types.Unalias(ty).(*types.Named)
	if !ok || n.Obj().Pkg() == nil || n.Obj().Pkg().Path() != statusPath {
		return "", false
	}
	name := n.Obj().Name()
	return name, name == "Status" || name == "Error"
}

func isTargetPtr(ty types.Type) bool {
	p, ok := types.Unalias(ty).Underlying().(*types.Pointer)
	if !ok {
		return false
	}
	_, ok = isTargetNamed(p.Elem())
	return ok
}

type scanResult struct {
	scanned    []string
	violations []string
	fieldReads map[string]int // enclosing function in internal/status -> count
	rawCalls   []string
}

// scan type-checks the packages of the closure that depend on internal/status (and itself),
// keeping those accepted by keep, and checks them.
func scan(t *testing.T, dir string, keep func(listPkg) bool, patterns ...string) scanResult {
	t.Helper()
	pkgs := goList(t, dir, patterns...)
	exports := map[string]string{}
	for _, p := range pkgs {
		exports[p.ImportPath] = p.Export
	}
	fset := token.NewFileSet()
	imp := importer.ForCompiler(fset, "gc", func(path string) (io.ReadCloser, error) {
		f := exports[path]
		if f == "" {
			return nil, fmt.Errorf("no export data for %s", path)
		}
		return os.Open(f)
	})
	res := scanResult{fieldReads: map[string]int{}}
	for _, p := range pkgs {
		if p.Standard || !keep(p) {
			continue
		}
		dep := p.ImportPath == statusPath
		for _, d := range p.Deps {
			dep = dep || d == statusPath
		}
		if !dep {
			continue
		}
		if len(p.CgoFiles) > 0 {
			res.violations = append(res.violations, p.ImportPath+": has cgo files, not scanned")
			continue
		}
		var files []*ast.File
		for _, f := range p.GoFiles {
			af, err := parser.ParseFile(fset, filepath.Join(p.Dir, f), nil, parser.SkipObjectResolution)
			if err != nil {
				t.Fatal(err)
			}
			files = append(files, af)
		}
		info := &types.Info{
			Types:      map[ast.Expr]types.TypeAndValue{},
			Uses:       map[*ast.Ident]types.Object{},
			Defs:       map[*ast.Ident]types.Object{},
			Selections: map[*ast.SelectorExpr]*types.Selection{},
		}
		conf := types.Config{Importer: imp}
		if _, err := conf.Check(p.ImportPath, fset, files, info); err != nil {
			t.Fatalf("type-checking %s: %v", p.ImportPath, err)
		}
		res.scanned = append(res.scanned, p.ImportPath)
		for _, f := range files {
			checkFile(fset, p.ImportPath, f, info, &res)
		}
	}
	return res
}

// fieldSel: se selects the field s of Status or Error.
func fieldSel(info *types.Info, se *ast.SelectorExpr) bool {
	sel := info.Selections[se]
	if sel == nil || sel.Kind() != types.FieldVal {
		return false
	}
	v := sel.Obj().(*types.Var)
	if v.Name() != "s" || v.Pkg() == nil || v.Pkg().Path() != statusPath {
		return false
	}
	recv := sel.Recv()
	if p, ok := types.Unalias(recv).(*types.Pointer); ok {
		recv = p.Elem()
	}
	_, ok := isTargetNamed(recv)
	return ok
}

// chainHasField: the lvalue e reaches the field s of a Status/Error through selectors, indexing,
// dereferences and parentheses.
func chainHasField(info *types.Info, e ast.Expr) bool {
	for {
		switch x := e.(type) {
		case *ast.ParenExpr:
			e = x.X
		case *ast.SelectorExpr:
			if fieldSel(info, x) {
				return true
			}
			e = x.X
		case *ast.IndexExpr:
			e = x.X
		case *ast.StarExpr:
			e = x.X
		default:
			return false
		}
	}
}

func funcKey(fd *ast.FuncDecl) string {
	if fd == nil {
		return "<package level>"
	}
	if fd.Recv != nil && len(fd.Recv.List) == 1 {
		rt := fd.Recv.List[0].Type
		if s, ok := rt.(*ast.StarExpr); ok {
			rt = s.X
		}
		if id, ok := rt.(*ast.Ident); ok {
			return id.Name + "." + fd.Name.Name
		}
	}
	return fd.Name.Name
}

func checkFile(fset *token.FileSet, pkg string, f *ast.File, info *types.Info, res *scanResult) {
	// The parent of every node, built first (checkRawCall looks at nodes after the call).
	parent := map[ast.Node]ast.Node{}
	var pstack []ast.Node
	ast.Inspect(f, func(n ast.Node) bool {
		if n == nil {
			pstack = pstack[:len(pstack)-1]
			return false
		}
		if len(pstack) > 0 {
			parent[n] = pstack[len(pstack)-1]
		}
		pstack = append(pstack, n)
		return true
	})
	var stack []ast.Node
	var fn *ast.FuncDecl
	report := func(n ast.Node, msg string) {
		res.violations = append(res.violations, fmt.Sprintf("%s: %s (in %s)", fset.Position(n.Pos()), msg, funcKey(fn)))
	}
	checkLHS := func(n ast.Node, lhs ast.Expr) {
		if chainHasField(info, lhs) {
			report(n, "write through the field s of a Status/Error")
		}
		if name, ok := isTargetNamed(info.TypeOf(lhs)); ok {
			report(n, "whole-struct write of a "+name)
		}
	}
	ast.Inspect(f, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return false
		}
		stack = append(stack, n)
		if fd, ok := n.(*ast.FuncDecl); ok {
			fn = fd
		}
		switch x := n.(type) {
		case *ast.AssignStmt:
			for _, l := range x.Lhs {
				if id, ok := l.(*ast.Ident); ok && (x.Tok == token.DEFINE || id.Name == "_") {
					continue // a new variable (a copy), or the blank identifier
				}
				checkLHS(x, l)
			}
		case *ast.IncDecStmt:
			checkLHS(x, x.X)
		case *ast.RangeStmt:
			if x.Tok == token.ASSIGN {
				for _, l := range []ast.Expr{x.Key, x.Value} {
					if l != nil {
						checkLHS(x, l)
					}
				}
			}
		case *ast.UnaryExpr:
			if x.Op == token.AND {
				if chainHasField(info, x.X) {
					report(x, "address of the field s of a Status/Error")
				}
				if _, ok := ast.Unparen(x.X).(*ast.CompositeLit); !ok {
					if name, ok := isTargetNamed(info.TypeOf(x.X)); ok {
						report(x, "address of an existing "+name)
					}
				}
			}
		case *ast.CallExpr:
			if tv, ok := info.Types[x.Fun]; ok && tv.IsType() && len(x.Args) == 1 {
				if b, ok := tv.Type.(*types.Basic); ok && b.Kind() == types.UnsafePointer && isTargetPtr(info.TypeOf(x.Args[0])) {
					report(x, "unsafe.Pointer of a *Status/*Error")
				}
			}
		case *ast.SelectorExpr:
			if fieldSel(info, x) {
				if pkg != statusPath {
					report(x, "read of the field s outside internal/status")
				} else {
					res.fieldReads[funcKey(fn)]++
					if !statusFieldReaders[funcKey(fn)] {
						report(x, "read of the field s in a function not listed in statusFieldReaders")
					}
				}
			}
		case *ast.Ident:
			if obj, ok := info.Uses[x].(*types.Func); ok && obj.Pkg() != nil && obj.Pkg().Path() == statusPath && obj.Name() == "RawStatusProto" && pkg != statusPath {
				res.rawCalls = append(res.rawCalls, fmt.Sprintf("%s (in %s)", fset.Position(x.Pos()), funcKey(fn)))
				checkRawCall(fset, pkg, x, parent, stack, info, report)
			}
		}
		return true
	})
}

// checkRawCall: the call is `p := istatus.RawStatusProto(st)` and p is used only as
// p.GetDetails(), proto.Marshal(p) or pretty.ToJSON(p).
func checkRawCall(fset *token.FileSet, pkg string, id *ast.Ident, parent map[ast.Node]ast.Node, stack []ast.Node, info *types.Info, report func(ast.Node, string)) {
	if pkg != "google.golang.org/grpc/internal/transport" {
		report(id, "RawStatusProto called outside internal/transport")
		return
	}
	// Climb to the call and its assignment.
	var call *ast.CallExpr
	var asg *ast.AssignStmt
	for i := len(stack) - 1; i >= 0 && asg == nil; i-- {
		switch x := stack[i].(type) {
		case *ast.CallExpr:
			if call == nil {
				call = x
			}
		case *ast.AssignStmt:
			asg = x
		}
	}
	if call == nil || asg == nil || len(asg.Lhs) != 1 || len(asg.Rhs) != 1 || asg.Rhs[0] != call {
		report(id, "RawStatusProto's result not bound by p := RawStatusProto(...)")
		return
	}
	lid, ok := asg.Lhs[0].(*ast.Ident)
	if !ok {
		report(id, "RawStatusProto's result not bound to a variable")
		return
	}
	obj := info.Defs[lid]
	// The variable's scope is the enclosing if statement: search its uses there.
	var scopeNode ast.Node = asg
	for p := parent[asg]; p != nil; p = parent[p] {
		scopeNode = p
		if _, ok := p.(*ast.IfStmt); ok {
			break
		}
	}
	ast.Inspect(scopeNode, func(n ast.Node) bool {
		u, ok := n.(*ast.Ident)
		if !ok || info.Uses[u] != obj {
			return true
		}
		switch p := parent[u].(type) {
		case *ast.SelectorExpr:
			if p.Sel.Name == "GetDetails" {
				return true
			}
		case *ast.CallExpr:
			if se, ok := p.Fun.(*ast.SelectorExpr); ok {
				if x, ok := se.X.(*ast.Ident); ok && ((x.Name == "proto" && se.Sel.Name == "Marshal") || (x.Name == "pretty" && se.Sel.Name == "ToJSON")) {
					return true
				}
			}
		}
		report(u, "RawStatusProto's result used other than GetDetails/proto.Marshal/pretty.ToJSON")
		return true
	})
}

func summarize(t *testing.T, name string, res scanResult) {
	t.Helper()
	sort.Strings(res.scanned)
	t.Logf("%s: scanned %d packages depending on internal/status", name, len(res.scanned))
	for _, v := range res.violations {
		t.Errorf("%s: %s", name, v)
	}
}

// TestNoStatusWriteEtcd: the etcd client, server (etcdserver and its gRPC API; embed's extra
// imports, cmux, the journal writer, are outside the examples module) and cache closures (the main
// examples module, the etcd fork at the etcd pin).
func TestNoStatusWriteEtcd(t *testing.T) {
	dir, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	res := scan(t, dir, func(listPkg) bool { return true },
		"go.etcd.io/etcd/client/v3",
		"go.etcd.io/etcd/api/v3/v3rpc/rpctypes",
		"go.etcd.io/etcd/server/v3/etcdserver",
		"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc",
		"go.etcd.io/etcd/cache/v3",
		"google.golang.org/grpc/status",
	)
	summarize(t, "etcd", res)
	if len(res.scanned) < 30 {
		t.Errorf("scanned only %d packages: the closure is not what the test assumes", len(res.scanned))
	}
	// internal/status itself was scanned, and its readers are the listed ones.
	found := false
	for _, p := range res.scanned {
		found = found || p == statusPath
	}
	if !found {
		t.Errorf("internal/status not scanned")
	}
	for k := range statusFieldReaders {
		if res.fieldReads[k] == 0 {
			t.Errorf("statusFieldReaders lists %s, which reads no field s (the list is stale)", k)
		}
	}
	t.Logf("field s read in: %v", res.fieldReads)
	// The two server-side calls of RawStatusProto (http2_server.go WriteHeader-less WriteStatus
	// paths), both read-only.
	if len(res.rawCalls) != 2 {
		t.Errorf("RawStatusProto calls: %v, expected the two of internal/transport/http2_server.go", res.rawCalls)
	}
	for _, c := range res.rawCalls {
		if !strings.Contains(c, "http2_server.go") {
			t.Errorf("RawStatusProto call outside http2_server.go: %s", c)
		}
	}
}

// TestNoStatusWriteK8s: the Kubernetes packages of the etcd3 storage's closure (the watcherctx
// module, which requires k8s.io/apiserver; grpc v1.84.0 as in the main module).
func TestNoStatusWriteK8s(t *testing.T) {
	dir, err := filepath.Abs("../watcherctx")
	if err != nil {
		t.Fatal(err)
	}
	res := scan(t, dir, func(p listPkg) bool {
		return p.Module != nil && strings.HasPrefix(p.Module.Path, "k8s.io/")
	}, "k8s.io/apiserver/pkg/storage/etcd3")
	summarize(t, "k8s", res)
	found := false
	for _, p := range res.scanned {
		found = found || p == "k8s.io/apiserver/pkg/storage/etcd3"
	}
	if !found {
		t.Errorf("k8s.io/apiserver/pkg/storage/etcd3 not scanned: %v", res.scanned)
	}
}

// TestScannerDetects: the scanner reports each kind of write on a small package written here
// (a negative control: a scan that reports nothing on these is broken).
func TestScannerDetects(t *testing.T) {
	src := `package bad

import (
	"unsafe"

	"google.golang.org/grpc/status"
	"google.golang.org/grpc/codes"
)

func wholeStruct(e interface{ GRPCStatus() *status.Status }) {
	s := e.GRPCStatus()
	*s = *status.New(codes.OK, "")
}

func addr(s *status.Status) *status.Status { return &*s }

func viaUnsafe(s *status.Status) unsafe.Pointer { return unsafe.Pointer(s) }
`
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, "bad.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	dir, _ := filepath.Abs("../..")
	pkgs := goList(t, dir, "google.golang.org/grpc/status", "google.golang.org/grpc/codes")
	exports := map[string]string{}
	for _, p := range pkgs {
		exports[p.ImportPath] = p.Export
	}
	imp := importer.ForCompiler(fset, "gc", func(path string) (io.ReadCloser, error) {
		if exports[path] == "" {
			return nil, fmt.Errorf("no export data for %s", path)
		}
		return os.Open(exports[path])
	})
	info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Uses: map[*ast.Ident]types.Object{},
		Defs: map[*ast.Ident]types.Object{}, Selections: map[*ast.SelectorExpr]*types.Selection{}}
	if _, err := (&types.Config{Importer: imp}).Check("bad", fset, []*ast.File{af}, info); err != nil {
		t.Fatal(err)
	}
	var res scanResult
	res.fieldReads = map[string]int{}
	checkFile(fset, "bad", af, info, &res)
	want := []string{"whole-struct write of a Status", "address of an existing Status", "unsafe.Pointer of a *Status/*Error"}
	for _, w := range want {
		ok := false
		for _, v := range res.violations {
			ok = ok || strings.Contains(v, w)
		}
		if !ok {
			t.Errorf("scanner missed %q; reported %v", w, res.violations)
		}
	}
}
