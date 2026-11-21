// Command authmed lists what etcd registers on its client port, for etc/auth-mediation-check.py
// (notes/auth-mediation-scope.md, §2.1):
//
//	authmed ETCD_SRC GRPC_SRC
//
// ETCD_SRC is a checkout of etcd at the pinned revision (etc/goose.py's project `etcd`), GRPC_SRC
// the source of google.golang.org/grpc at the version etcd's server module requires. It prints, one
// per line, sorted:
//
//	grpc ORIGIN /SERVICE/METHOD unary|stream
//	hook ORIGIN EXPR
//	http ORIGIN PATH
//
// A `grpc` line is a method of a service registered by a `<pkg>.Register<X>Server(gs, ...)` call in
// one of the registering functions below (ORIGIN): the descriptor `Register<X>Server` passes to
// `RegisterService`, read from the generated `*_grpc.pb.go` (its `ServiceName`, `Methods` and
// `Streams`). A `hook` line is any other call in a registering function that is passed the gRPC
// server (an embedder's hook, such as `serviceRegister`). An `http` line is a handler registration
// (`Handle`/`HandleFunc` on a mux) reached from the client port's HTTP setup: `serveClients`'
// `etcdhttp.Handle*` calls (followed through the package's own functions and methods, by name) and
// `createMux`; PATH is the path's string constant when it is one, its source text otherwise.
//
// It reads syntax only (go/parser, no type checking, no module download). Exits 1 if a registration
// cannot be resolved: a gate must not pass on what it could not read.
package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

// The functions that register gRPC services on the client port's server: file (under ETCD_SRC),
// receiver type ("" for a function) and name, and the ORIGIN printed for them.
var grpcRegistrars = []struct{ file, recv, name, origin string }{
	{"server/etcdserver/api/v3rpc/grpc.go", "", "Server", "v3rpc.Server"},
	{"server/embed/serve.go", "serveCtx", "serve", "embed.serveCtx.serve"},
}

// The client port's HTTP setup.
var httpRoots = []struct{ file, recv, name, origin string }{
	{"server/embed/etcd.go", "Etcd", "serveClients", "embed.Etcd.serveClients"},
	{"server/embed/serve.go", "serveCtx", "createMux", "embed.serveCtx.createMux"},
}

var fset = token.NewFileSet()
var out []string
var failed bool

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "authmed: "+format+"\n", args...)
	failed = true
}

func parseFile(path string) *ast.File {
	f, err := parser.ParseFile(fset, path, nil, 0)
	if err != nil {
		fail("%v", err)
		return nil
	}
	return f
}

// parseDir parses the non-test Go files of a directory.
func parseDir(dir string) []*ast.File {
	ents, err := os.ReadDir(dir)
	if err != nil {
		fail("%v", err)
		return nil
	}
	var fs []*ast.File
	for _, e := range ents {
		n := e.Name()
		if e.IsDir() || !strings.HasSuffix(n, ".go") || strings.HasSuffix(n, "_test.go") {
			continue
		}
		if f := parseFile(filepath.Join(dir, n)); f != nil {
			fs = append(fs, f)
		}
	}
	return fs
}

func recvName(fd *ast.FuncDecl) string {
	if fd.Recv == nil || len(fd.Recv.List) == 0 {
		return ""
	}
	t := fd.Recv.List[0].Type
	if s, ok := t.(*ast.StarExpr); ok {
		t = s.X
	}
	if id, ok := t.(*ast.Ident); ok {
		return id.Name
	}
	return "?"
}

func findFunc(fs []*ast.File, recv, name string) (*ast.FuncDecl, *ast.File) {
	for _, f := range fs {
		for _, d := range f.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == name && recvName(fd) == recv && fd.Body != nil {
				return fd, f
			}
		}
	}
	return nil, nil
}

func src(e ast.Expr) string {
	var b bytes.Buffer
	printer.Fprint(&b, fset, e)
	return b.String()
}

// imports maps a file's import names to their paths.
func imports(f *ast.File) map[string]string {
	m := map[string]string{}
	for _, is := range f.Imports {
		p, _ := strconv.Unquote(is.Path.Value)
		n := p[strings.LastIndex(p, "/")+1:]
		if is.Name != nil {
			n = is.Name.Name
		}
		m[n] = p
	}
	return m
}

// modules maps the Go module paths of the etcd checkout to their directories.
func modules(etcd string) map[string]string {
	m := map[string]string{}
	filepath.WalkDir(etcd, func(p string, d os.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		if d.IsDir() && (d.Name() == ".git" || d.Name() == "tools" || d.Name() == "tests") {
			return filepath.SkipDir
		}
		if d.Name() == "go.mod" {
			b, _ := os.ReadFile(p)
			for _, l := range strings.Split(string(b), "\n") {
				if strings.HasPrefix(l, "module ") {
					m[strings.TrimSpace(strings.TrimPrefix(l, "module "))] = filepath.Dir(p)
				}
			}
		}
		return nil
	})
	return m
}

var etcdMods map[string]string
var grpcSrc string

// pkgDir resolves an import path to its directory: a module of the etcd checkout, or grpc's.
func pkgDir(imp string) string {
	if imp == "google.golang.org/grpc" || strings.HasPrefix(imp, "google.golang.org/grpc/") {
		return filepath.Join(grpcSrc, strings.TrimPrefix(imp, "google.golang.org/grpc"))
	}
	best := ""
	for mp := range etcdMods {
		if (imp == mp || strings.HasPrefix(imp, mp+"/")) && len(mp) > len(best) {
			best = mp
		}
	}
	if best == "" {
		return ""
	}
	return filepath.Join(etcdMods[best], strings.TrimPrefix(imp, best))
}

func strLit(e ast.Expr) (string, bool) {
	if bl, ok := e.(*ast.BasicLit); ok && bl.Kind == token.STRING {
		s, err := strconv.Unquote(bl.Value)
		return s, err == nil
	}
	return "", false
}

// descMethods reads a `grpc.ServiceDesc` literal: its service name, methods and streams.
func descMethods(fs []*ast.File, name string) (string, []string, []string, bool) {
	for _, f := range fs {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, sp := range gd.Specs {
				vs := sp.(*ast.ValueSpec)
				for i, n := range vs.Names {
					if n.Name != name || i >= len(vs.Values) {
						continue
					}
					cl, ok := vs.Values[i].(*ast.CompositeLit)
					if !ok {
						return "", nil, nil, false
					}
					var svc string
					var ms, ss []string
					for _, el := range cl.Elts {
						kv, ok := el.(*ast.KeyValueExpr)
						if !ok {
							continue
						}
						key := src(kv.Key)
						switch key {
						case "ServiceName":
							svc, _ = strLit(kv.Value)
						case "Methods", "Streams":
							lst, ok := kv.Value.(*ast.CompositeLit)
							if !ok {
								return "", nil, nil, false
							}
							for _, m := range lst.Elts {
								mc, ok := m.(*ast.CompositeLit)
								if !ok {
									return "", nil, nil, false
								}
								for _, f := range mc.Elts {
									fkv, ok := f.(*ast.KeyValueExpr)
									if !ok {
										continue
									}
									k := src(fkv.Key)
									if k == "MethodName" || k == "StreamName" {
										s, ok := strLit(fkv.Value)
										if !ok {
											return "", nil, nil, false
										}
										if key == "Methods" {
											ms = append(ms, s)
										} else {
											ss = append(ss, s)
										}
									}
								}
							}
						}
					}
					return svc, ms, ss, svc != ""
				}
			}
		}
	}
	return "", nil, nil, false
}

var registerRe = regexp.MustCompile(`^Register(\w+)Server$`)

// registerDesc finds the descriptor `Register<X>Server` passes to `RegisterService`.
func registerDesc(fs []*ast.File, fn string) string {
	fd, _ := findFunc(fs, "", fn)
	if fd == nil {
		return ""
	}
	desc := ""
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		c, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		if se, ok := c.Fun.(*ast.SelectorExpr); ok && se.Sel.Name == "RegisterService" && len(c.Args) == 2 {
			if u, ok := c.Args[0].(*ast.UnaryExpr); ok && u.Op == token.AND {
				if id, ok := u.X.(*ast.Ident); ok {
					desc = id.Name
				}
			}
		}
		return true
	})
	return desc
}

func grpcRegs(etcd string) {
	for _, r := range grpcRegistrars {
		f := parseFile(filepath.Join(etcd, r.file))
		if f == nil {
			continue
		}
		fd, _ := findFunc([]*ast.File{f}, r.recv, r.name)
		if fd == nil {
			fail("%s: no function %s.%s", r.file, r.recv, r.name)
			continue
		}
		imp := imports(f)
		// the gRPC server variables: assigned from v3rpc.Server or grpc.NewServer
		gsVars := map[string]bool{}
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			if as, ok := n.(*ast.AssignStmt); ok && len(as.Lhs) == 1 && len(as.Rhs) == 1 {
				if c, ok := as.Rhs[0].(*ast.CallExpr); ok {
					s := src(c.Fun)
					if s == "v3rpc.Server" || s == "grpc.NewServer" {
						gsVars[src(as.Lhs[0])] = true
					}
				}
			}
			return true
		})
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok || len(c.Args) == 0 {
				return true
			}
			if !gsVars[src(c.Args[0])] {
				return true
			}
			if _, ok := c.Fun.(*ast.FuncLit); ok {
				// a deferred cleanup closure (`defer func(gs *grpc.Server) {...}(gs)`): stops the
				// server on an error, registers nothing
				return true
			}
			se, isSel := c.Fun.(*ast.SelectorExpr)
			var m []string
			if isSel {
				m = registerRe.FindStringSubmatch(se.Sel.Name)
			}
			pkgID, isPkg := ast.Expr(nil), false
			if isSel {
				if id, ok := se.X.(*ast.Ident); ok && imp[id.Name] != "" {
					pkgID, isPkg = id, true
				}
			}
			if m == nil || !isPkg {
				out = append(out, fmt.Sprintf("hook %s %s", r.origin, src(c.Fun)))
				return true
			}
			path := imp[pkgID.(*ast.Ident).Name]
			dir := pkgDir(path)
			if dir == "" {
				fail("%s: cannot resolve %s", r.origin, path)
				return true
			}
			pfs := parseDir(dir)
			desc := registerDesc(pfs, se.Sel.Name)
			if desc == "" {
				fail("%s: %s.%s: no RegisterService(&desc, ...)", r.origin, path, se.Sel.Name)
				return true
			}
			svc, ms, ss, ok := descMethods(pfs, desc)
			if !ok {
				fail("%s: %s.%s: cannot read %s", r.origin, path, se.Sel.Name, desc)
				return true
			}
			for _, x := range ms {
				out = append(out, fmt.Sprintf("grpc %s /%s/%s unary", r.origin, svc, x))
			}
			for _, x := range ss {
				out = append(out, fmt.Sprintf("grpc %s /%s/%s stream", r.origin, svc, x))
			}
			return true
		})
	}
}

// consts maps a package's string constants to their values.
func consts(fs []*ast.File) map[string]string {
	m := map[string]string{}
	for _, f := range fs {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.CONST {
				continue
			}
			for _, sp := range gd.Specs {
				vs := sp.(*ast.ValueSpec)
				for i, n := range vs.Names {
					if i < len(vs.Values) {
						if s, ok := strLit(vs.Values[i]); ok {
							m[n.Name] = s
						}
					}
				}
			}
		}
	}
	return m
}

// handles collects the Handle/HandleFunc registrations of a function's body, following calls of
// the package's own functions and methods (by name).
func handles(fs []*ast.File, cs map[string]string, fd *ast.FuncDecl, origin string, seen map[*ast.FuncDecl]bool) {
	if seen[fd] {
		return
	}
	seen[fd] = true
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		c, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		var name string
		switch fn := c.Fun.(type) {
		case *ast.Ident:
			name = fn.Name
		case *ast.SelectorExpr:
			name = fn.Sel.Name
			if (name == "Handle" || name == "HandleFunc") && len(c.Args) == 2 {
				p := src(c.Args[0])
				if s, ok := strLit(c.Args[0]); ok {
					p = s
				} else if id, ok := c.Args[0].(*ast.Ident); ok && cs[id.Name] != "" {
					p = cs[id.Name]
				}
				fname := fd.Name.Name
				if r := recvName(fd); r != "" {
					fname = r + "." + fname
				}
				out = append(out, fmt.Sprintf("http %s %s", origin+":"+fname, strings.ReplaceAll(p, " ", "")))
				return true
			}
		}
		for _, f := range fs {
			for _, d := range f.Decls {
				if g, ok := d.(*ast.FuncDecl); ok && g.Name.Name == name && g.Body != nil {
					handles(fs, cs, g, origin, seen)
				}
			}
		}
		return true
	})
}

func httpRegs(etcd string) {
	for _, r := range httpRoots {
		f := parseFile(filepath.Join(etcd, r.file))
		if f == nil {
			continue
		}
		fd, _ := findFunc([]*ast.File{f}, r.recv, r.name)
		if fd == nil {
			fail("%s: no function %s.%s", r.file, r.recv, r.name)
			continue
		}
		imp := imports(f)
		// the mux registrations in the root itself
		embedFs := []*ast.File{f}
		handles(embedFs, consts(embedFs), &ast.FuncDecl{Name: fd.Name, Recv: fd.Recv, Body: &ast.BlockStmt{List: onlyHandles(fd.Body)}}, r.origin, map[*ast.FuncDecl]bool{})
		// the other packages' Handle* functions it calls
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			se, ok := c.Fun.(*ast.SelectorExpr)
			if !ok || !strings.HasPrefix(se.Sel.Name, "Handle") {
				return true
			}
			id, ok := se.X.(*ast.Ident)
			if !ok || imp[id.Name] == "" {
				return true
			}
			dir := pkgDir(imp[id.Name])
			if dir == "" {
				fail("%s: cannot resolve %s", r.origin, imp[id.Name])
				return true
			}
			pfs := parseDir(dir)
			g, _ := findFunc(pfs, "", se.Sel.Name)
			if g == nil {
				fail("%s: no function %s.%s", r.origin, imp[id.Name], se.Sel.Name)
				return true
			}
			handles(pfs, consts(pfs), g, id.Name+"."+se.Sel.Name, map[*ast.FuncDecl]bool{})
			return true
		})
	}
}

// onlyHandles keeps a body's statements as they are (the root's own Handle calls are collected
// without following its other calls, which are another package's or the server's).
func onlyHandles(b *ast.BlockStmt) []ast.Stmt {
	var l []ast.Stmt
	ast.Inspect(b, func(n ast.Node) bool {
		if c, ok := n.(*ast.CallExpr); ok {
			if se, ok := c.Fun.(*ast.SelectorExpr); ok && (se.Sel.Name == "Handle" || se.Sel.Name == "HandleFunc") && len(c.Args) == 2 {
				l = append(l, &ast.ExprStmt{X: c})
			}
		}
		return true
	})
	return l
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: authmed ETCD_SRC GRPC_SRC")
		os.Exit(2)
	}
	etcd := os.Args[1]
	grpcSrc = os.Args[2]
	etcdMods = modules(etcd)
	grpcRegs(etcd)
	httpRegs(etcd)
	if failed {
		os.Exit(1)
	}
	sort.Strings(out)
	prev := ""
	for _, l := range out {
		if l != prev {
			fmt.Println(l)
		}
		prev = l
	}
}
