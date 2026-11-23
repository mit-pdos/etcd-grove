package main

// fieldUses: the check that a struct with a ghost field is never compared, hashed or reflected
// on, on the type-checked packages of the struct's Go module.

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
)

// listed: the fields of `go list -json` this check reads.
type listed struct {
	ImportPath string
	Dir        string
	GoFiles    []string
	Export     string
	Standard   bool
	ImportMap  map[string]string
	Module     *struct{ Path string }
	Error      *struct{ Err string }
}

// moduleRoot: the directory of the go.mod that holds dir.
func moduleRoot(dir string) (string, error) {
	d, err := filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	for {
		if _, err := os.Stat(filepath.Join(d, "go.mod")); err == nil {
			return d, nil
		}
		p := filepath.Dir(d)
		if p == d {
			return "", fmt.Errorf("%s: in no Go module", dir)
		}
		d = p
	}
}

type importerFunc func(path string) (*types.Package, error)

func (f importerFunc) Import(path string) (*types.Package, error) { return f(path) }

// fieldUses type-checks the packages of the Go module that holds dir (the package that declares
// the ghost fields) and reports any use of the struct types `structs` (of that package) that may
// observe a ghost field:
//   - an operand of == or != (or of a switch's comparisons) whose type contains one of them (the
//     struct itself, or an array or struct type with such an element or field);
//   - a map type whose key type contains one;
//   - a conversion (explicit or implicit: an assignment, an argument, a result, an element of a
//     composite literal, a send, a map index) to an interface type of a value whose type reaches
//     one (contains it, or a pointer, slice, array, map or struct field that reaches it): an
//     interface value can be compared, hashed and reflected on (reflect, fmt, encoders);
//   - a type argument of a generic instantiation that reaches one;
//   - unsafe.Sizeof, Alignof or Offsetof of an expression whose type reaches one.
func fieldUses(dir string, structs map[string]bool) []string {
	root, err := moduleRoot(dir)
	if err != nil {
		return []string{err.Error()}
	}
	cmd := exec.Command("go", "list", "-e", "-export", "-deps", "-json", "./...")
	cmd.Dir = root
	var out, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &stderr
	if err := cmd.Run(); err != nil {
		return []string{fmt.Sprintf("%s: go list: %v: %s", root, err, stderr.String())}
	}
	var pkgs []*listed
	exports := map[string]string{}
	dec := json.NewDecoder(&out)
	for {
		var p listed
		if err := dec.Decode(&p); err == io.EOF {
			break
		} else if err != nil {
			return []string{fmt.Sprintf("%s: go list output: %v", root, err)}
		}
		if p.Error != nil {
			return []string{fmt.Sprintf("%s: go list: %s", p.ImportPath, p.Error.Err)}
		}
		exports[p.ImportPath] = p.Export
		pkgs = append(pkgs, &p)
	}
	absDir, _ := filepath.Abs(dir)
	var mainMod, declPath string
	for _, p := range pkgs {
		if d, _ := filepath.Abs(p.Dir); d == absDir {
			declPath = p.ImportPath
			if p.Module != nil {
				mainMod = p.Module.Path
			}
		}
	}
	if declPath == "" {
		return []string{fmt.Sprintf("%s: not a package of the module %s", dir, root)}
	}
	fset := token.NewFileSet()
	gc := importer.ForCompiler(fset, "gc", func(path string) (io.ReadCloser, error) {
		e, ok := exports[path]
		if !ok || e == "" {
			return nil, fmt.Errorf("no export data for %s", path)
		}
		return os.Open(e)
	})
	u := &uses{structs: structs, declPath: declPath, fset: fset}
	for _, p := range pkgs {
		if p.Standard || p.Module == nil || p.Module.Path != mainMod {
			continue
		}
		var files []*ast.File
		for _, f := range p.GoFiles {
			af, err := parser.ParseFile(fset, filepath.Join(p.Dir, f), nil, parser.SkipObjectResolution)
			if err != nil {
				return []string{err.Error()}
			}
			files = append(files, af)
		}
		info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{},
			Uses: map[*ast.Ident]types.Object{}, Instances: map[*ast.Ident]types.Instance{}}
		im := p.ImportMap
		conf := types.Config{Importer: importerFunc(func(path string) (*types.Package, error) {
			if m, ok := im[path]; ok {
				path = m
			}
			return gc.Import(path)
		})}
		if _, err := conf.Check(p.ImportPath, fset, files, info); err != nil {
			return []string{fmt.Sprintf("%s: type-checking: %v", p.ImportPath, err)}
		}
		u.info = info
		for _, f := range files {
			u.file(f)
		}
	}
	return u.errs
}

type uses struct {
	structs  map[string]bool // the struct types' names, in declPath
	declPath string
	fset     *token.FileSet
	info     *types.Info
	errs     []string
}

func (u *uses) errorf(pos token.Pos, format string, args ...any) {
	u.errs = append(u.errs, fmt.Sprintf("%s: %s", u.fset.Position(pos), fmt.Sprintf(format, args...)))
}

func (u *uses) isStruct(t types.Type) bool {
	n, ok := types.Unalias(t).(*types.Named)
	if !ok {
		return false
	}
	o := n.Obj()
	return o.Pkg() != nil && o.Pkg().Path() == u.declPath && u.structs[o.Name()]
}

// contains: t is one of the structs, or an array or struct (by value) with such an element or field.
func (u *uses) contains(t types.Type) bool {
	return u.walk(t, false, map[types.Type]bool{})
}

// reaches: t contains one of the structs, through values, pointers, slices, arrays, maps and
// struct fields.
func (u *uses) reaches(t types.Type) bool {
	return u.walk(t, true, map[types.Type]bool{})
}

func (u *uses) walk(t types.Type, refs bool, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	if u.isStruct(t) {
		return true
	}
	switch t := t.Underlying().(type) {
	case *types.Array:
		return u.walk(t.Elem(), refs, seen)
	case *types.Struct:
		for i := 0; i < t.NumFields(); i++ {
			if u.walk(t.Field(i).Type(), refs, seen) {
				return true
			}
		}
	case *types.Pointer:
		return refs && u.walk(t.Elem(), refs, seen)
	case *types.Slice:
		return refs && u.walk(t.Elem(), refs, seen)
	case *types.Map:
		return refs && (u.walk(t.Key(), refs, seen) || u.walk(t.Elem(), refs, seen))
	}
	return false
}

func (u *uses) typeOf(e ast.Expr) types.Type {
	if tv, ok := u.info.Types[e]; ok {
		return tv.Type
	}
	return nil
}

// conv checks a conversion of e to the type dst.
func (u *uses) conv(e ast.Expr, dst types.Type) {
	if e == nil || dst == nil {
		return
	}
	if _, ok := types.Unalias(dst).(*types.TypeParam); ok {
		return // a type argument's (checked at the instantiation)
	}
	src := u.typeOf(e)
	if src == nil || types.IsInterface(src) || !types.IsInterface(dst) {
		return
	}
	if u.reaches(src) {
		u.errorf(e.Pos(), "converts a value of type %s, which reaches a struct with a ghost field, "+
			"to an interface (where it may be compared, hashed or reflected on)", src)
	}
}

// mapKeys reports the map types in t whose keys contain a struct.
func (u *uses) mapKeys(pos token.Pos, t types.Type, seen map[types.Type]bool) {
	if t == nil || seen[t] {
		return
	}
	seen[t] = true
	switch t := types.Unalias(t).(type) {
	case *types.Named:
		if t.Obj().Pkg() == nil || t.Obj().Pkg().Path() != u.declPath {
			// a named type of another package cannot name the struct (but through type arguments)
			for i := 0; i < t.TypeArgs().Len(); i++ {
				u.mapKeys(pos, t.TypeArgs().At(i), seen)
			}
			return
		}
		u.mapKeys(pos, t.Underlying(), seen)
	case *types.Map:
		if u.contains(t.Key()) {
			u.errorf(pos, "a map type whose key contains a struct with a ghost field: %s", t)
		}
		u.mapKeys(pos, t.Key(), seen)
		u.mapKeys(pos, t.Elem(), seen)
	case *types.Pointer:
		u.mapKeys(pos, t.Elem(), seen)
	case *types.Slice:
		u.mapKeys(pos, t.Elem(), seen)
	case *types.Array:
		u.mapKeys(pos, t.Elem(), seen)
	case *types.Chan:
		u.mapKeys(pos, t.Elem(), seen)
	case *types.Struct:
		for i := 0; i < t.NumFields(); i++ {
			u.mapKeys(pos, t.Field(i).Type(), seen)
		}
	case *types.Signature:
		for _, tu := range []*types.Tuple{t.Params(), t.Results()} {
			for i := 0; i < tu.Len(); i++ {
				u.mapKeys(pos, tu.At(i).Type(), seen)
			}
		}
	}
}

func (u *uses) file(f *ast.File) {
	// the signatures of the enclosing functions, for return statements
	var sigs []*types.Signature
	var visit func(n ast.Node) bool
	visit = func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncDecl:
			if o, ok := u.info.Defs[n.Name].(*types.Func); ok && n.Body != nil {
				sigs = append(sigs, o.Type().(*types.Signature))
				ast.Inspect(n.Body, visit)
				sigs = sigs[:len(sigs)-1]
			}
			return false
		case *ast.FuncLit:
			if s, ok := u.typeOf(n).(*types.Signature); ok {
				sigs = append(sigs, s)
				ast.Inspect(n.Body, visit)
				sigs = sigs[:len(sigs)-1]
			}
			return false
		case *ast.BinaryExpr:
			if n.Op == token.EQL || n.Op == token.NEQ {
				if u.contains(u.typeOf(n.X)) || u.contains(u.typeOf(n.Y)) {
					u.errorf(n.Pos(), "compares a struct with a ghost field (%s)", n.Op)
				}
				// comparing with an interface converts the other operand
				if tx, ty := u.typeOf(n.X), u.typeOf(n.Y); tx != nil && ty != nil {
					u.conv(n.X, ty)
					u.conv(n.Y, tx)
				}
			}
		case *ast.SwitchStmt:
			if n.Tag != nil {
				tt := u.typeOf(n.Tag)
				if u.contains(tt) {
					u.errorf(n.Pos(), "switches on a struct with a ghost field")
				}
				for _, cl := range n.Body.List {
					for _, e := range cl.(*ast.CaseClause).List {
						if u.contains(u.typeOf(e)) {
							u.errorf(e.Pos(), "compares a struct with a ghost field (a switch case)")
						}
						u.conv(e, tt)
						if ct := u.typeOf(e); ct != nil {
							u.conv(n.Tag, ct)
						}
					}
				}
			}
		case *ast.AssignStmt:
			if n.Tok == token.ASSIGN && len(n.Lhs) == len(n.Rhs) {
				for i := range n.Lhs {
					u.conv(n.Rhs[i], u.typeOf(n.Lhs[i]))
				}
			}
		case *ast.ValueSpec:
			if n.Type != nil {
				t := u.typeOf(n.Type)
				for _, v := range n.Values {
					u.conv(v, t)
				}
			}
		case *ast.ReturnStmt:
			if len(sigs) > 0 {
				res := sigs[len(sigs)-1].Results()
				if res.Len() == len(n.Results) {
					for i, r := range n.Results {
						u.conv(r, res.At(i).Type())
					}
				}
			}
		case *ast.SendStmt:
			if ch, ok := u.typeOf(n.Chan).Underlying().(*types.Chan); ok {
				u.conv(n.Value, ch.Elem())
			}
		case *ast.IndexExpr:
			if t := u.typeOf(n.X); t != nil {
				if m, ok := t.Underlying().(*types.Map); ok {
					u.conv(n.Index, m.Key())
				}
			}
		case *ast.CompositeLit:
			u.compositeLit(n)
		case *ast.CallExpr:
			u.call(n)
		case *ast.Ident:
			if o := u.info.Defs[n]; o != nil {
				u.mapKeys(n.Pos(), o.Type(), map[types.Type]bool{})
			}
			if inst, ok := u.info.Instances[n]; ok {
				for i := 0; i < inst.TypeArgs.Len(); i++ {
					if u.reaches(inst.TypeArgs.At(i)) {
						u.errorf(n.Pos(), "instantiates %s with a type that reaches a struct "+
							"with a ghost field", n.Name)
					}
				}
			}
		}
		if e, ok := n.(ast.Expr); ok {
			if t := u.typeOf(e); t != nil {
				u.mapKeys(e.Pos(), t, map[types.Type]bool{})
			}
		}
		return true
	}
	ast.Inspect(f, visit)
}

func (u *uses) compositeLit(n *ast.CompositeLit) {
	t := u.typeOf(n)
	if t == nil {
		return
	}
	switch ut := t.Underlying().(type) {
	case *types.Struct:
		for i, e := range n.Elts {
			if kv, ok := e.(*ast.KeyValueExpr); ok {
				if k, ok := kv.Key.(*ast.Ident); ok {
					for j := 0; j < ut.NumFields(); j++ {
						if ut.Field(j).Name() == k.Name {
							u.conv(kv.Value, ut.Field(j).Type())
						}
					}
				}
			} else if i < ut.NumFields() {
				u.conv(e, ut.Field(i).Type())
			}
		}
	case *types.Slice, *types.Array, *types.Map:
		var key, elem types.Type
		switch ut := ut.(type) {
		case *types.Slice:
			elem = ut.Elem()
		case *types.Array:
			elem = ut.Elem()
		case *types.Map:
			key, elem = ut.Key(), ut.Elem()
		}
		for _, e := range n.Elts {
			if kv, ok := e.(*ast.KeyValueExpr); ok {
				if key != nil {
					u.conv(kv.Key, key)
				}
				u.conv(kv.Value, elem)
			} else {
				u.conv(e, elem)
			}
		}
	}
}

func (u *uses) call(n *ast.CallExpr) {
	ft := u.info.Types[n.Fun]
	if ft.IsType() {
		if len(n.Args) == 1 {
			u.conv(n.Args[0], ft.Type)
		}
		return
	}
	var fid *ast.Ident
	switch f := ast.Unparen(n.Fun).(type) {
	case *ast.Ident:
		fid = f
	case *ast.SelectorExpr:
		fid = f.Sel
	}
	if fid != nil {
		if b, ok := u.info.Uses[fid].(*types.Builtin); ok {
			switch b.Name() {
			case "panic", "print", "println":
				for _, a := range n.Args {
					u.conv(a, types.NewInterfaceType(nil, nil))
				}
			case "append":
				if len(n.Args) > 0 && !n.Ellipsis.IsValid() {
					if s, ok := u.typeOf(n.Args[0]).Underlying().(*types.Slice); ok {
						for _, a := range n.Args[1:] {
							u.conv(a, s.Elem())
						}
					}
				}
			case "Sizeof", "Alignof", "Offsetof":
				for _, a := range n.Args {
					if u.reaches(u.typeOf(a)) {
						u.errorf(n.Pos(), "unsafe.%s of a value that reaches a struct with a ghost field", b.Name())
					}
				}
			}
			return
		}
	}
	sig, ok := ft.Type.(*types.Signature)
	if !ok {
		if ft.Type != nil {
			sig, ok = ft.Type.Underlying().(*types.Signature)
		}
		if !ok {
			return
		}
	}
	ps := sig.Params()
	for i, a := range n.Args {
		var pt types.Type
		switch {
		case sig.Variadic() && i >= ps.Len()-1:
			last := ps.At(ps.Len() - 1).Type()
			if n.Ellipsis.IsValid() {
				pt = last
			} else if s, ok := last.Underlying().(*types.Slice); ok {
				pt = s.Elem()
			}
		case i < ps.Len():
			pt = ps.At(i).Type()
		}
		u.conv(a, pt)
	}
	// a method call through an interface converts nothing; a method value of an embedded
	// interface neither
}
