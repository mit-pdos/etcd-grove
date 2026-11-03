// Command prophcheck checks that a prophecy patch of a Go file only adds prophecy statements:
//
//	prophcheck ORIG PATCHED [ORIG PATCHED]...
//
// For each pair, PATCHED with its prophecy statements erased must be ORIG, as syntax trees
// (positions, comments and formatting do not matter). A prophecy statement is one of
//
//	NAME := primitive.NewProph()
//	NAME.ResolveBool(E)   NAME.ResolveU64(E)
//	if C { S... } else { S... }   (no init statement; the branches, the else optional or an
//	                               `else if` of the same kind, hold prophecy statements only)
//
// where NAME is a name that does not occur in ORIG, declared by the patch's own NewProph, and E and
// C are read-only expressions: identifiers, literals, field selections, dereferences, indexing,
// slicing, type assertions, unary (but `<-` and `&`) and binary operations of read-only
// expressions, and calls of `len`, `cap` and conversions to predeclared basic types (names the file
// does not redeclare). The import "github.com/goose-lang/primitive" is erased too when ORIG does
// not have it (and then ORIG must not use the name `primitive`).
//
// Why this is enough: Go's prophecy operations do nothing (goose-lang/primitive's proph.go), and
// a read-only expression has no effect: evaluated, it either produces a value or fails (a nil
// dereference, an out-of-range index, a failed assertion, a division by zero, a data race). So
// every execution of ORIG is, step for step, an execution of PATCHED with the extra reads and
// prophecy operations, unless one of those reads fails; the patched program may have more failing
// executions, never fewer behaviors. A proof that PATCHED does not fail therefore covers ORIG.
// Exits 1, printing what is wrong, if a pair does not check.
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
)

const primPath = "github.com/goose-lang/primitive"

var conversions = map[string]bool{
	"bool": true, "string": true, "int": true, "int8": true, "int16": true, "int32": true,
	"int64": true, "uint": true, "uint8": true, "uint16": true, "uint32": true, "uint64": true,
	"uintptr": true, "byte": true, "rune": true, "float32": true, "float64": true,
	"len": true, "cap": true,
}

type checker struct {
	file      string
	errs      []string
	origNames map[string]bool // every identifier of ORIG
	declared  map[string]bool // the prophecies the patch declares
	shadowed  map[string]bool // the names the original file or its package declares
	fset      *token.FileSet
}

func (c *checker) errorf(pos token.Pos, format string, args ...any) {
	c.errs = append(c.errs, fmt.Sprintf("%s: %s", c.fset.Position(pos), fmt.Sprintf(format, args...)))
}

// readOnly reports whether evaluating e can have no effect (it may fail).
func (c *checker) readOnly(e ast.Expr) bool {
	switch e := e.(type) {
	case *ast.Ident, *ast.BasicLit:
		return true
	case *ast.ParenExpr:
		return c.readOnly(e.X)
	case *ast.SelectorExpr:
		return c.readOnly(e.X)
	case *ast.StarExpr:
		return c.readOnly(e.X)
	case *ast.IndexExpr:
		return c.readOnly(e.X) && c.readOnly(e.Index)
	case *ast.SliceExpr:
		for _, x := range []ast.Expr{e.Low, e.High, e.Max} {
			if x != nil && !c.readOnly(x) {
				return false
			}
		}
		return c.readOnly(e.X)
	case *ast.TypeAssertExpr:
		return e.Type != nil && c.readOnly(e.X)
	case *ast.UnaryExpr:
		return e.Op != token.ARROW && e.Op != token.AND && c.readOnly(e.X)
	case *ast.BinaryExpr:
		return c.readOnly(e.X) && c.readOnly(e.Y)
	case *ast.CallExpr:
		f, ok := e.Fun.(*ast.Ident)
		if !ok || !conversions[f.Name] || c.shadowed[f.Name] || e.Ellipsis.IsValid() {
			return false
		}
		for _, a := range e.Args {
			if !c.readOnly(a) {
				return false
			}
		}
		return true
	}
	return false
}

func isNewProph(s ast.Stmt) (string, bool) {
	a, ok := s.(*ast.AssignStmt)
	if !ok || a.Tok != token.DEFINE || len(a.Lhs) != 1 || len(a.Rhs) != 1 {
		return "", false
	}
	id, ok := a.Lhs[0].(*ast.Ident)
	call, ok2 := a.Rhs[0].(*ast.CallExpr)
	if !ok || !ok2 || len(call.Args) != 0 {
		return "", false
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "NewProph" {
		return "", false
	}
	pkg, ok := sel.X.(*ast.Ident)
	if !ok || pkg.Name != "primitive" {
		return "", false
	}
	return id.Name, true
}

// prophStmt reports whether s is a prophecy statement (checking its parts when it is one).
func (c *checker) prophStmt(s ast.Stmt) bool {
	if name, ok := isNewProph(s); ok {
		if c.origNames[name] {
			// the original's own prophecy (or a name it uses): not the patch's
			return false
		}
		c.declared[name] = true
		return true
	}
	switch s := s.(type) {
	case *ast.ExprStmt:
		call, ok := s.X.(*ast.CallExpr)
		if !ok {
			return false
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || (sel.Sel.Name != "ResolveBool" && sel.Sel.Name != "ResolveU64") {
			return false
		}
		recv, ok := sel.X.(*ast.Ident)
		if !ok || c.origNames[recv.Name] {
			return false
		}
		if !c.declared[recv.Name] {
			c.errorf(s.Pos(), "resolves %s, which the patch has not declared before", recv.Name)
		}
		if len(call.Args) != 1 || call.Ellipsis.IsValid() || !c.readOnly(call.Args[0]) {
			c.errorf(s.Pos(), "the resolution of %s: its argument is not one read-only expression",
				recv.Name)
		}
		return true
	case *ast.IfStmt:
		if s.Init != nil || !c.readOnly(s.Cond) || !c.allProph(s.Body.List) {
			return false
		}
		switch e := s.Else.(type) {
		case nil:
			return true
		case *ast.BlockStmt:
			return c.allProph(e.List)
		case *ast.IfStmt:
			return c.prophStmt(e)
		}
	}
	return false
}

func (c *checker) allProph(l []ast.Stmt) bool {
	for _, s := range l {
		if !c.prophStmt(s) {
			return false
		}
	}
	return true
}

// erase removes the prophecy statements of every statement list under n.
func (c *checker) erase(n ast.Node) {
	filter := func(l []ast.Stmt) []ast.Stmt {
		out := l[:0:0]
		for _, s := range l {
			if !c.prophStmt(s) {
				out = append(out, s)
			}
		}
		return out
	}
	ast.Inspect(n, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.BlockStmt:
			n.List = filter(n.List)
		case *ast.CaseClause:
			n.Body = filter(n.Body)
		case *ast.CommClause:
			n.Body = filter(n.Body)
		}
		return true
	})
}

// eraseImport removes the import of primitive.
func eraseImport(f *ast.File) {
	keep := f.Decls[:0:0]
	for _, d := range f.Decls {
		g, ok := d.(*ast.GenDecl)
		if ok && g.Tok == token.IMPORT {
			specs := g.Specs[:0:0]
			for _, sp := range g.Specs {
				if p, _ := strconv.Unquote(sp.(*ast.ImportSpec).Path.Value); p == primPath &&
					sp.(*ast.ImportSpec).Name == nil {
					continue
				}
				specs = append(specs, sp)
			}
			g.Specs = specs
			if len(specs) == 0 {
				continue
			}
		}
		keep = append(keep, d)
	}
	f.Decls = keep
	f.Imports = nil
}

func importsPrim(f *ast.File) bool {
	for _, sp := range f.Imports {
		if p, _ := strconv.Unquote(sp.Path.Value); p == primPath && sp.Name == nil {
			return true
		}
	}
	return false
}

var (
	posType   = reflect.TypeOf(token.Pos(0))
	cgType    = reflect.TypeOf((*ast.CommentGroup)(nil))
	objType   = reflect.TypeOf((*ast.Object)(nil))
	scopeType = reflect.TypeOf((*ast.Scope)(nil))
)

// equal compares syntax trees, ignoring positions, comments and resolution objects.
func equal(a, b reflect.Value) bool {
	if a.Kind() != b.Kind() {
		return false
	}
	switch a.Kind() {
	case reflect.Pointer, reflect.Interface:
		if a.IsNil() || b.IsNil() {
			return a.IsNil() == b.IsNil()
		}
		if a.Kind() == reflect.Interface && a.Elem().Type() != b.Elem().Type() {
			return false
		}
		return equal(a.Elem(), b.Elem())
	case reflect.Struct:
		for i := 0; i < a.NumField(); i++ {
			t := a.Type().Field(i).Type
			if t == posType || t == cgType || t == objType || t == scopeType ||
				a.Type().Field(i).Name == "Comments" || a.Type().Field(i).Name == "Imports" ||
				a.Type().Field(i).Name == "Unresolved" {
				continue
			}
			if !equal(a.Field(i), b.Field(i)) {
				return false
			}
		}
		return true
	case reflect.Slice:
		if a.Len() != b.Len() {
			return false
		}
		for i := 0; i < a.Len(); i++ {
			if !equal(a.Index(i), b.Index(i)) {
				return false
			}
		}
		return true
	default:
		if a.Type() == posType {
			return true
		}
		return a.Interface() == b.Interface()
	}
}

// declaredNames: the names declared in f (at any level).
func declaredNames(f *ast.File, out map[string]bool) {
	add := func(ids ...*ast.Ident) {
		for _, id := range ids {
			if id != nil {
				out[id.Name] = true
			}
		}
	}
	ast.Inspect(f, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncDecl:
			add(n.Name)
		case *ast.Field:
			add(n.Names...)
		case *ast.ValueSpec:
			add(n.Names...)
		case *ast.TypeSpec:
			add(n.Name)
		case *ast.ImportSpec:
			add(n.Name)
		case *ast.LabeledStmt:
			add(n.Label)
		case *ast.AssignStmt:
			if n.Tok == token.DEFINE {
				for _, l := range n.Lhs {
					if id, ok := l.(*ast.Ident); ok {
						add(id)
					}
				}
			}
		case *ast.RangeStmt:
			if n.Tok == token.DEFINE {
				for _, l := range []ast.Expr{n.Key, n.Value} {
					if id, ok := l.(*ast.Ident); ok {
						add(id)
					}
				}
			}
		}
		return true
	})
}

// packageNames: the package-level names declared by the other Go files of orig's directory.
func packageNames(orig string, out map[string]bool) {
	dir := filepath.Dir(orig)
	ents, err := os.ReadDir(dir)
	if err != nil {
		return
	}
	fset := token.NewFileSet()
	for _, e := range ents {
		if e.IsDir() || !strings.HasSuffix(e.Name(), ".go") {
			continue
		}
		f, err := parser.ParseFile(fset, filepath.Join(dir, e.Name()), nil, parser.SkipObjectResolution)
		if err != nil {
			continue
		}
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				if d.Recv == nil {
					out[d.Name.Name] = true
				}
			case *ast.GenDecl:
				for _, sp := range d.Specs {
					switch sp := sp.(type) {
					case *ast.ValueSpec:
						for _, id := range sp.Names {
							out[id.Name] = true
						}
					case *ast.TypeSpec:
						out[sp.Name.Name] = true
					}
				}
			}
		}
	}
}

func check(orig, patched string) []string {
	fset := token.NewFileSet()
	mode := parser.SkipObjectResolution
	of, err := parser.ParseFile(fset, orig, nil, mode)
	if err != nil {
		return []string{err.Error()}
	}
	pf, err := parser.ParseFile(fset, patched, nil, mode)
	if err != nil {
		return []string{err.Error()}
	}
	c := &checker{file: patched, origNames: map[string]bool{}, declared: map[string]bool{},
		shadowed: map[string]bool{}, fset: fset}
	declaredNames(of, c.shadowed)
	packageNames(orig, c.shadowed)
	ast.Inspect(of, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			c.origNames[id.Name] = true
		}
		return true
	})
	patchedImports := importsPrim(pf)
	if importsPrim(pf) && !importsPrim(of) {
		if c.origNames["primitive"] {
			c.errorf(pf.Pos(), "adds the import of primitive to a file that uses the name `primitive`")
		}
		eraseImport(pf)
		eraseImport(of)
	}
	c.erase(pf)
	if len(c.declared) > 0 && !patchedImports {
		c.errorf(pf.Pos(), "declares prophecies but does not import %q (unnamed)", primPath)
	}
	if !equal(reflect.ValueOf(of), reflect.ValueOf(pf)) {
		c.errs = append(c.errs, fmt.Sprintf("%s: with its prophecy statements erased, it is not %s "+
			"(a patch may only add prophecy statements; see etc/prophcheck/main.go)", patched, orig))
	}
	return c.errs
}

func main() {
	args := os.Args[1:]
	if len(args) == 0 || len(args)%2 != 0 {
		fmt.Fprintln(os.Stderr, "usage: prophcheck ORIG PATCHED [ORIG PATCHED]...")
		os.Exit(2)
	}
	bad := false
	for i := 0; i < len(args); i += 2 {
		for _, e := range check(args[i], args[i+1]) {
			fmt.Println(e)
			bad = true
		}
	}
	if bad {
		os.Exit(1)
	}
}
