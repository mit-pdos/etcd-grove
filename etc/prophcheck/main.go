// Command prophcheck checks that a prophecy patch of Go files only adds ghost code:
//
//	prophcheck ORIG PATCHED [ORIG PATCHED]...
//
// The pairs are the files a project's prophecy patches change (etc/proph_patch.py): ORIG, the
// project's file, and PATCHED, the same file with the patches applied. PATCHED with its ghost
// code erased must be ORIG, as syntax trees (positions, comments and formatting do not matter).
// notes/proph-patch-rule.md lists the checks. The ghost code is:
//
// Ghost declarations (top level), each with a name that occurs in no Go file of ORIG's directory
// (the package; "fresh"):
//
//	var NAME = primitive.NewProph()                      a ghost variable
//	type T struct { ...; NAME primitive.ProphId; ... }   a ghost field (in a struct type of ORIG)
//	func NAME(PARAMS) { BODY }                           a ghost helper
//	func (R RT) NAME(PARAMS) { BODY }                    a ghost helper method (NAME unexported)
//
// A ghost field is unexported, has no tag, and the program must not compare its struct with ==,
// use it in a map key, or reflect on it: checked on the type-checked packages of the field's Go
// module (fieldUses, uses.go). A helper has no results and no type parameters, and its BODY holds
// only helper statements:
//
//	P.ResolveBool(E)   P.ResolveU64(E)        P a ghost prophecy: a ghost variable, X.F for a
//	                                          ghost field F, or a local prophecy of the patch
//	H(E...)   X.H(E...)                       a call of a ghost helper (helpers do not recurse)
//	NAME := E   NAME = E   NAME op= E         NAME a local of the helper (a parameter or a local
//	NAME++   NAME--                           it defines)
//	if C { S... } else { S... }               (no init statement)
//	for I := E; I < E2; I++ { S... }          (the body does not assign I)
//	{ S... }   return                         (no results)
//
// Ghost statements (in any statement list of the PATCHED file outside the helpers):
//
//	NAME := primitive.NewProph()              NAME not in ORIG: a local prophecy
//	P.ResolveBool(E)   P.ResolveU64(E)        P a ghost prophecy
//	H(E...)   X.H(E...)                       a call of a ghost helper
//	X.F = primitive.NewProph()                F a ghost field
//	if C { S... } else { S... }               (no init statement; the branches, the else
//	                                           optional or an `else if` of the same kind, hold
//	                                           ghost statements only)
//
// and, in a composite literal, a ghost field's keyed element `F: primitive.NewProph()`; and the
// import "github.com/goose-lang/primitive" when ORIG does not have it (ORIG must then not use the
// name `primitive`). E, E2, C and X are read-only expressions: identifiers, literals, field
// selections, dereferences, indexing, slicing, type assertions, `&` of a field selection or of an
// indexing, unary (but `<-`) and binary operations of read-only expressions, and calls of `len`,
// `cap` and conversions to predeclared basic types (names the package does not redeclare).
//
// Why this is enough: Go's prophecy operations do nothing (goose-lang/primitive's proph.go). A
// read-only expression has no effect: evaluated, it either produces a value or fails (a nil
// dereference, an out-of-range index, a failed assertion, a division by zero, a data race). A
// helper only evaluates read-only expressions, writes its own locals, resolves prophecies and
// calls helpers, and it terminates or fails: its calls do not recurse, and its loops count up to a
// bound (run without interleaving, which some execution does, the bound is fixed). The ghost
// declarations' names are fresh, so the original code cannot refer to them; a ghost field changes
// what the program could observe of its struct only through ==, hashing or reflection, which it
// does not use on it; a ghost method is unexported, so it changes no interface the type
// implements. So every execution of ORIG is, step for step, an execution of PATCHED with the
// extra ghost steps, unless one of those fails: the patched program may have more failing
// executions, never fewer behaviors, and a proof that PATCHED does not fail covers ORIG.
//
// Exits 1, printing what is wrong, if the files do not check.
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"reflect"
	"sort"
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

// pkgGhost: the ghost declarations of one package (the PATCHED files of ORIG's directory).
type pkgGhost struct {
	origDir, dir string
	origNames    map[string]bool          // every identifier of the original package's Go files
	shadowed     map[string]bool          // the names the original package declares
	vars         map[string]bool          // ghost variables
	fields       map[string]string        // ghost field -> its struct type
	helpers      map[string]*ast.FuncDecl // ghost helpers (functions and methods) by name
	calls        map[string]map[string]bool
}

type checker struct {
	errs []string
	fset *token.FileSet
	pkg  *pkgGhost
	// the local prophecies the patch declares (NAME := primitive.NewProph()) in the current file
	declared map[string]bool
	// the identifiers of the current ORIG file
	origNames map[string]bool
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
		if e.Op == token.AND {
			// the address of a field or an element (no allocation, no effect)
			switch x := e.X.(type) {
			case *ast.SelectorExpr, *ast.IndexExpr:
				return c.readOnly(x)
			}
			return false
		}
		return e.Op != token.ARROW && c.readOnly(e.X)
	case *ast.BinaryExpr:
		return c.readOnly(e.X) && c.readOnly(e.Y)
	case *ast.CallExpr:
		f, ok := e.Fun.(*ast.Ident)
		if !ok || !conversions[f.Name] || c.pkg.shadowed[f.Name] || c.pkg.helpers[f.Name] != nil ||
			c.pkg.vars[f.Name] || e.Ellipsis.IsValid() {
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

// isNewProph reports whether e is `primitive.NewProph()`.
func isNewProph(e ast.Expr) bool {
	call, ok := e.(*ast.CallExpr)
	if !ok || len(call.Args) != 0 || call.Ellipsis.IsValid() {
		return false
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "NewProph" {
		return false
	}
	pkg, ok := sel.X.(*ast.Ident)
	return ok && pkg.Name == "primitive"
}

func isNewProphStmt(s ast.Stmt) (string, bool) {
	a, ok := s.(*ast.AssignStmt)
	if !ok || a.Tok != token.DEFINE || len(a.Lhs) != 1 || len(a.Rhs) != 1 || !isNewProph(a.Rhs[0]) {
		return "", false
	}
	id, ok := a.Lhs[0].(*ast.Ident)
	if !ok {
		return "", false
	}
	return id.Name, true
}

// isProphType reports whether e is `primitive.ProphId`.
func isProphType(e ast.Expr) bool {
	sel, ok := e.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "ProphId" {
		return false
	}
	pkg, ok := sel.X.(*ast.Ident)
	return ok && pkg.Name == "primitive"
}

// ghostProph reports whether p is a ghost prophecy: a ghost variable, X.F for a ghost field F and
// a read-only X, or a local prophecy the patch declared; locals: a helper's locals (which shadow).
func (c *checker) ghostProph(p ast.Expr, locals map[string]bool) bool {
	switch p := p.(type) {
	case *ast.Ident:
		if locals[p.Name] {
			return false
		}
		return c.pkg.vars[p.Name] || (!c.origNames[p.Name] && c.declared[p.Name])
	case *ast.SelectorExpr:
		_, ok := c.pkg.fields[p.Sel.Name]
		return ok && c.readOnly(p.X)
	}
	return false
}

// resolveCall reports whether call is a resolution `P.ResolveBool(E)` / `P.ResolveU64(E)` of a
// ghost prophecy (and reports a bad argument).
func (c *checker) resolveCall(call *ast.CallExpr, locals map[string]bool) bool {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok || (sel.Sel.Name != "ResolveBool" && sel.Sel.Name != "ResolveU64") {
		return false
	}
	if id, ok := sel.X.(*ast.Ident); ok && !c.origNames[id.Name] && !c.pkg.origNames[id.Name] &&
		!c.pkg.vars[id.Name] && !locals[id.Name] && !c.declared[id.Name] {
		c.errorf(call.Pos(), "resolves %s, which the patch has not declared before", id.Name)
		return true
	}
	if !c.ghostProph(sel.X, locals) {
		return false
	}
	if len(call.Args) != 1 || call.Ellipsis.IsValid() || !c.readOnly(call.Args[0]) {
		c.errorf(call.Pos(), "a resolution: its argument is not one read-only expression")
	}
	return true
}

// helperCall reports whether call calls a ghost helper (`H(E...)` or `X.H(E...)`; reporting
// arguments that are not read-only), and its name.
func (c *checker) helperCall(call *ast.CallExpr, locals map[string]bool) (string, bool) {
	var name string
	switch f := call.Fun.(type) {
	case *ast.Ident:
		h := c.pkg.helpers[f.Name]
		if h == nil || h.Recv != nil || locals[f.Name] {
			return "", false
		}
		name = f.Name
	case *ast.SelectorExpr:
		// a method name fresh in the package and unexported: only the ghost method has it
		h := c.pkg.helpers[f.Sel.Name]
		if h == nil || h.Recv == nil {
			return "", false
		}
		if !c.readOnly(f.X) {
			c.errorf(call.Pos(), "a call of the ghost helper %s: its receiver is not read-only", f.Sel.Name)
		}
		name = f.Sel.Name
	default:
		return "", false
	}
	if call.Ellipsis.IsValid() {
		c.errorf(call.Pos(), "a call of the ghost helper %s with ...", name)
	}
	for _, a := range call.Args {
		if !c.readOnly(a) {
			c.errorf(a.Pos(), "a call of the ghost helper %s: an argument is not read-only", name)
		}
	}
	return name, true
}

// ghostStmt reports whether s is a ghost statement (checking its parts when it is one).
func (c *checker) ghostStmt(s ast.Stmt) bool {
	if name, ok := isNewProphStmt(s); ok {
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
		if c.resolveCall(call, nil) {
			return true
		}
		_, ok = c.helperCall(call, nil)
		return ok
	case *ast.AssignStmt:
		// X.F = primitive.NewProph(), F a ghost field
		if s.Tok != token.ASSIGN || len(s.Lhs) != 1 || len(s.Rhs) != 1 || !isNewProph(s.Rhs[0]) {
			return false
		}
		sel, ok := s.Lhs[0].(*ast.SelectorExpr)
		if !ok {
			return false
		}
		_, ok = c.pkg.fields[sel.Sel.Name]
		return ok && c.readOnly(sel.X)
	case *ast.IfStmt:
		if s.Init != nil || !c.readOnly(s.Cond) || !c.allGhost(s.Body.List) {
			return false
		}
		switch e := s.Else.(type) {
		case nil:
			return true
		case *ast.BlockStmt:
			return c.allGhost(e.List)
		case *ast.IfStmt:
			return c.ghostStmt(e)
		}
	}
	return false
}

func (c *checker) allGhost(l []ast.Stmt) bool {
	for _, s := range l {
		if !c.ghostStmt(s) {
			return false
		}
	}
	return true
}

func copyLocals(m map[string]bool) map[string]bool {
	out := map[string]bool{}
	for k, v := range m {
		out[k] = v
	}
	return out
}

// helperBody checks the statements of a ghost helper's body (locals: its parameters and the
// locals it has defined; calls: the helpers it calls).
func (c *checker) helperBody(l []ast.Stmt, locals, calls map[string]bool) {
	for _, s := range l {
		c.helperStmt(s, locals, calls)
	}
}

func (c *checker) helperStmt(s ast.Stmt, locals, calls map[string]bool) {
	switch s := s.(type) {
	case *ast.ExprStmt:
		if call, ok := s.X.(*ast.CallExpr); ok {
			if c.resolveCall(call, locals) {
				return
			}
			if name, ok := c.helperCall(call, locals); ok {
				calls[name] = true
				return
			}
		}
		c.errorf(s.Pos(), "a ghost helper's statement that is neither a resolution nor a ghost helper's call")
	case *ast.AssignStmt:
		if len(s.Lhs) != len(s.Rhs) {
			c.errorf(s.Pos(), "a ghost helper's assignment of a multi-valued expression")
		}
		for _, r := range s.Rhs {
			if !c.readOnly(r) {
				c.errorf(r.Pos(), "a ghost helper's assignment: not a read-only expression")
			}
		}
		for _, l := range s.Lhs {
			id, ok := l.(*ast.Ident)
			switch {
			case !ok:
				c.errorf(l.Pos(), "a ghost helper assigns to something other than its own locals")
			case s.Tok == token.DEFINE:
				if id.Name != "_" {
					locals[id.Name] = true
				}
			case !locals[id.Name]:
				c.errorf(l.Pos(), "a ghost helper assigns to %s, not one of its own locals", id.Name)
			}
		}
	case *ast.IncDecStmt:
		if id, ok := s.X.(*ast.Ident); !ok || !locals[id.Name] {
			c.errorf(s.Pos(), "a ghost helper increments something other than its own locals")
		}
	case *ast.IfStmt:
		if s.Init != nil {
			c.errorf(s.Pos(), "a ghost helper's if with an init statement")
		}
		if !c.readOnly(s.Cond) {
			c.errorf(s.Cond.Pos(), "a ghost helper's if: its condition is not read-only")
		}
		c.helperBody(s.Body.List, copyLocals(locals), calls)
		if s.Else != nil {
			c.helperStmt(s.Else, copyLocals(locals), calls)
		}
	case *ast.BlockStmt:
		c.helperBody(s.List, copyLocals(locals), calls)
	case *ast.ForStmt:
		c.helperFor(s, locals, calls)
	case *ast.ReturnStmt:
		if len(s.Results) != 0 {
			c.errorf(s.Pos(), "a ghost helper returns a value")
		}
	default:
		c.errorf(s.Pos(), "a ghost helper's statement of a kind not allowed (%T)", s)
	}
}

// helperFor checks `for I := E; I < E2; I++ { S... }`, the body not assigning I.
func (c *checker) helperFor(s *ast.ForStmt, locals, calls map[string]bool) {
	ok := func() bool {
		init, ok := s.Init.(*ast.AssignStmt)
		if !ok || init.Tok != token.DEFINE || len(init.Lhs) != 1 || len(init.Rhs) != 1 ||
			!c.readOnly(init.Rhs[0]) {
			return false
		}
		i, ok := init.Lhs[0].(*ast.Ident)
		if !ok || i.Name == "_" {
			return false
		}
		cond, ok := s.Cond.(*ast.BinaryExpr)
		if !ok || cond.Op != token.LSS || !c.readOnly(cond.Y) {
			return false
		}
		if ci, ok := cond.X.(*ast.Ident); !ok || ci.Name != i.Name {
			return false
		}
		post, ok := s.Post.(*ast.IncDecStmt)
		if !ok || post.Tok != token.INC {
			return false
		}
		pi, ok := post.X.(*ast.Ident)
		return ok && pi.Name == i.Name
	}()
	if !ok {
		c.errorf(s.Pos(), "a ghost helper's loop not of the form `for I := E; I < E2; I++`")
		return
	}
	inner := copyLocals(locals)
	// the counter is readable but not assignable in the body
	delete(inner, s.Init.(*ast.AssignStmt).Lhs[0].(*ast.Ident).Name)
	c.helperBody(s.Body.List, inner, calls)
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

// origPackage: the identifiers and the declared names of the Go files of dir (the original package).
func origPackage(dir string, idents, declared map[string]bool) {
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
		declaredNames(f, declared)
		ast.Inspect(f, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok {
				idents[id.Name] = true
			}
			return true
		})
	}
}

// erase removes the ghost statements of every statement list under n (outside the helpers,
// already removed), and the ghost fields' keyed elements of composite literals.
func (c *checker) erase(n ast.Node) {
	filter := func(l []ast.Stmt) []ast.Stmt {
		out := l[:0:0]
		for _, s := range l {
			if !c.ghostStmt(s) {
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
		case *ast.CompositeLit:
			out := n.Elts[:0:0]
			for _, e := range n.Elts {
				if kv, ok := e.(*ast.KeyValueExpr); ok {
					if k, ok := kv.Key.(*ast.Ident); ok {
						if _, ok := c.pkg.fields[k.Name]; ok && isNewProph(kv.Value) {
							continue
						}
					}
				}
				out = append(out, e)
			}
			n.Elts = out
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

// collect records the ghost declarations of pf (top-level declarations and struct fields whose
// names are fresh in the original package) in pkg, reporting added declarations of other kinds.
func collect(pf *ast.File, pkg *pkgGhost, errorf func(token.Pos, string, ...any)) {
	fresh := func(name string) bool { return name != "_" && !pkg.origNames[name] }
	for _, d := range pf.Decls {
		switch d := d.(type) {
		case *ast.FuncDecl:
			if d.Name.Name == "init" && d.Recv == nil {
				continue // an added init is not a ghost helper: erasure leaves it, and the check fails
			}
			if !fresh(d.Name.Name) {
				continue
			}
			if pkg.helpers[d.Name.Name] != nil {
				errorf(d.Pos(), "two ghost helpers named %s", d.Name.Name)
			}
			pkg.helpers[d.Name.Name] = d
		case *ast.GenDecl:
			for _, sp := range d.Specs {
				switch sp := sp.(type) {
				case *ast.ValueSpec:
					for _, id := range sp.Names {
						if !fresh(id.Name) {
							continue
						}
						if d.Tok == token.VAR {
							pkg.vars[id.Name] = true
						} else {
							errorf(id.Pos(), "adds the constant %s (a patch adds only ghost "+
								"variables, fields and helpers)", id.Name)
						}
					}
				case *ast.TypeSpec:
					if fresh(sp.Name.Name) {
						errorf(sp.Pos(), "adds the type %s (a patch adds only ghost variables, "+
							"fields and helpers)", sp.Name.Name)
						continue
					}
					st, ok := sp.Type.(*ast.StructType)
					if !ok {
						continue
					}
					for _, f := range st.Fields.List {
						for _, id := range f.Names {
							if fresh(id.Name) {
								pkg.fields[id.Name] = sp.Name.Name
							}
						}
					}
				}
			}
		}
	}
}

// eraseDecls checks pf's ghost declarations and removes them (and the ghost fields) from pf.
func (c *checker) eraseDecls(pf *ast.File) {
	keep := pf.Decls[:0:0]
	for _, d := range pf.Decls {
		switch d := d.(type) {
		case *ast.FuncDecl:
			if c.pkg.helpers[d.Name.Name] == d {
				c.checkHelper(d)
				continue
			}
		case *ast.GenDecl:
			if d.Tok == token.VAR {
				specs := d.Specs[:0:0]
				for _, sp := range d.Specs {
					vs := sp.(*ast.ValueSpec)
					ghost := false
					for _, id := range vs.Names {
						ghost = ghost || c.pkg.vars[id.Name]
					}
					if !ghost {
						specs = append(specs, sp)
						continue
					}
					if len(vs.Names) != 1 || len(vs.Values) != 1 || !isNewProph(vs.Values[0]) ||
						(vs.Type != nil && !isProphType(vs.Type)) {
						c.errorf(vs.Pos(), "a ghost variable must be declared alone, as "+
							"`var NAME = primitive.NewProph()`")
					}
				}
				if len(specs) == 0 && len(d.Specs) > 0 {
					continue // a declaration of ghost variables only
				}
				d.Specs = specs
			}
			if d.Tok == token.TYPE {
				for _, sp := range d.Specs {
					st, ok := sp.(*ast.TypeSpec).Type.(*ast.StructType)
					if !ok {
						continue
					}
					fl := st.Fields.List[:0:0]
					for _, f := range st.Fields.List {
						ghost := false
						for _, id := range f.Names {
							_, g := c.pkg.fields[id.Name]
							ghost = ghost || g
						}
						if !ghost {
							fl = append(fl, f)
							continue
						}
						if len(f.Names) != 1 || !isProphType(f.Type) || f.Tag != nil {
							c.errorf(f.Pos(), "a ghost field must be declared alone, as "+
								"`NAME primitive.ProphId` (no tag)")
						} else if ast.IsExported(f.Names[0].Name) {
							c.errorf(f.Pos(), "the ghost field %s is exported", f.Names[0].Name)
						}
					}
					st.Fields.List = fl
				}
			}
		}
		keep = append(keep, d)
	}
	pf.Decls = keep
}

// checkHelper checks a ghost helper's signature and body.
func (c *checker) checkHelper(d *ast.FuncDecl) {
	if d.Type.TypeParams != nil && len(d.Type.TypeParams.List) > 0 {
		c.errorf(d.Pos(), "the ghost helper %s has type parameters", d.Name.Name)
	}
	if d.Type.Results != nil && len(d.Type.Results.List) > 0 {
		c.errorf(d.Pos(), "the ghost helper %s has results", d.Name.Name)
	}
	if d.Recv != nil && ast.IsExported(d.Name.Name) {
		c.errorf(d.Pos(), "the ghost helper method %s is exported (it may change the interfaces "+
			"its type implements)", d.Name.Name)
	}
	if d.Body == nil {
		c.errorf(d.Pos(), "the ghost helper %s has no body", d.Name.Name)
		return
	}
	locals := map[string]bool{}
	var fields []*ast.Field
	if d.Recv != nil {
		fields = append(fields, d.Recv.List...)
	}
	fields = append(fields, d.Type.Params.List...)
	for _, f := range fields {
		for _, id := range f.Names {
			if id.Name != "_" {
				locals[id.Name] = true
			}
		}
	}
	calls := map[string]bool{}
	c.helperBody(d.Body.List, locals, calls)
	c.pkg.calls[d.Name.Name] = calls
}

// recursive: the ghost helpers that can call themselves.
func recursive(calls map[string]map[string]bool) []string {
	var out []string
	for n := range calls {
		seen := map[string]bool{}
		var reach func(string) bool
		reach = func(m string) bool {
			for k := range calls[m] {
				if k == n {
					return true
				}
				if !seen[k] {
					seen[k] = true
					if reach(k) {
						return true
					}
				}
			}
			return false
		}
		if reach(n) {
			out = append(out, n)
		}
	}
	sort.Strings(out)
	return out
}

// check checks the pairs (ORIG, PATCHED) and returns what is wrong.
func check(pairs [][2]string) []string {
	fset := token.NewFileSet()
	mode := parser.SkipObjectResolution
	var errs []string
	errorf := func(pos token.Pos, format string, args ...any) {
		errs = append(errs, fmt.Sprintf("%s: %s", fset.Position(pos), fmt.Sprintf(format, args...)))
	}
	type pair struct {
		orig, patched string
		of, pf        *ast.File
		pkg           *pkgGhost
	}
	pkgs := map[string]*pkgGhost{} // by ORIG's directory
	var order []string
	var ps []*pair
	for _, pr := range pairs {
		of, err := parser.ParseFile(fset, pr[0], nil, mode)
		if err != nil {
			errs = append(errs, err.Error())
			continue
		}
		pf, err := parser.ParseFile(fset, pr[1], nil, mode)
		if err != nil {
			errs = append(errs, err.Error())
			continue
		}
		dir := filepath.Dir(pr[0])
		pkg := pkgs[dir]
		if pkg == nil {
			pkg = &pkgGhost{origDir: dir, dir: filepath.Dir(pr[1]), origNames: map[string]bool{},
				shadowed: map[string]bool{}, vars: map[string]bool{}, fields: map[string]string{},
				helpers: map[string]*ast.FuncDecl{}, calls: map[string]map[string]bool{}}
			origPackage(dir, pkg.origNames, pkg.shadowed)
			pkgs[dir] = pkg
			order = append(order, dir)
		}
		ps = append(ps, &pair{orig: pr[0], patched: pr[1], of: of, pf: pf, pkg: pkg})
	}
	for _, p := range ps {
		collect(p.pf, p.pkg, errorf)
	}
	for _, p := range ps {
		c := &checker{fset: fset, pkg: p.pkg, declared: map[string]bool{}, origNames: map[string]bool{}}
		ast.Inspect(p.of, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok {
				c.origNames[id.Name] = true
			}
			return true
		})
		patchedImports := importsPrim(p.pf)
		if patchedImports && !importsPrim(p.of) {
			if c.origNames["primitive"] {
				c.errorf(p.pf.Pos(), "adds the import of primitive to a file that uses the name `primitive`")
			}
			eraseImport(p.pf)
			eraseImport(p.of)
		}
		c.eraseDecls(p.pf)
		c.erase(p.pf)
		if len(c.declared) > 0 && !patchedImports {
			c.errorf(p.pf.Pos(), "declares prophecies but does not import %q (unnamed)", primPath)
		}
		if !equal(reflect.ValueOf(p.of), reflect.ValueOf(p.pf)) {
			c.errs = append(c.errs, fmt.Sprintf("%s: with its ghost code erased, it is not %s "+
				"(a patch may only add ghost code; see etc/prophcheck/main.go)", p.patched, p.orig))
		}
		errs = append(errs, c.errs...)
	}
	for _, dir := range order {
		pkg := pkgs[dir]
		for _, n := range recursive(pkg.calls) {
			errs = append(errs, fmt.Sprintf("%s: the ghost helper %s can call itself (a helper "+
				"must terminate)", pkg.dir, n))
		}
		// ghost fields: the program must not compare, hash or reflect on their structs
		if len(pkg.fields) > 0 {
			structs := map[string]bool{}
			for _, t := range pkg.fields {
				structs[t] = true
			}
			errs = append(errs, fieldUses(pkg.dir, structs)...)
		}
	}
	return errs
}

func main() {
	args := os.Args[1:]
	if len(args) == 0 || len(args)%2 != 0 {
		fmt.Fprintln(os.Stderr, "usage: prophcheck ORIG PATCHED [ORIG PATCHED]...")
		os.Exit(2)
	}
	var pairs [][2]string
	for i := 0; i < len(args); i += 2 {
		pairs = append(pairs, [2]string{args[i], args[i+1]})
	}
	errs := check(pairs)
	for _, e := range errs {
		fmt.Println(e)
	}
	if len(errs) > 0 {
		os.Exit(1)
	}
}
