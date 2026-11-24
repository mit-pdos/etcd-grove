package ctxhyp

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// The context package never writes a *valueCtx's fields after WithValue builds it (so the
// spec's read-only points-to ↦□ is sound) and builds valueCtx only in WithValue: a scan of
// go1.27.3's context sources, type-checked, for assignments to fields of valueCtx and for
// composite literals of it, and for taking a field's address.
func TestValueCtxFieldsNeverWritten(t *testing.T) {
	dir := filepath.Join(runtime.GOROOT(), "src", "context")
	fset := token.NewFileSet()
	ents, _ := os.ReadDir(dir)
	var files []*ast.File
	for _, e := range ents {
		n := e.Name()
		if !strings.HasSuffix(n, ".go") || strings.HasSuffix(n, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, filepath.Join(dir, n), nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		files = append(files, f)
	}
	info := &types.Info{Selections: map[*ast.SelectorExpr]*types.Selection{}, Types: map[ast.Expr]types.TypeAndValue{}}
	conf := types.Config{Importer: importer.ForCompiler(fset, "source", nil)}
	if _, err := conf.Check("context", fset, files, info); err != nil {
		t.Fatal(err)
	}
	isValueCtxField := func(e ast.Expr) bool {
		se, ok := ast.Unparen(e).(*ast.SelectorExpr)
		if !ok {
			return false
		}
		sel := info.Selections[se]
		if sel == nil || sel.Kind() != types.FieldVal {
			return false
		}
		r := sel.Recv()
		if p, ok := r.(*types.Pointer); ok {
			r = p.Elem()
		}
		n, ok := r.(*types.Named)
		return ok && n.Obj().Name() == "valueCtx" && len(sel.Index()) == 1
	}
	lits, reads := 0, 0
	for _, f := range files {
		ast.Inspect(f, func(n ast.Node) bool {
			if e, ok := n.(ast.Expr); ok && isValueCtxField(e) {
				reads++ // every field selection (the scan sees them)
			}
			switch n := n.(type) {
			case *ast.AssignStmt:
				for _, l := range n.Lhs {
					if isValueCtxField(l) {
						t.Errorf("%s: writes a valueCtx field", fset.Position(n.Pos()))
					}
				}
			case *ast.IncDecStmt:
				if isValueCtxField(n.X) {
					t.Errorf("%s: writes a valueCtx field", fset.Position(n.Pos()))
				}
			case *ast.UnaryExpr:
				if n.Op == token.AND && isValueCtxField(n.X) {
					t.Errorf("%s: takes a valueCtx field's address", fset.Position(n.Pos()))
				}
			case *ast.CompositeLit:
				if tv, ok := info.Types[n]; ok {
					if nt, ok := tv.Type.(*types.Named); ok && nt.Obj().Name() == "valueCtx" {
						lits++
						t.Logf("%s: valueCtx literal", fset.Position(n.Pos()))
					}
				}
			}
			return true
		})
	}
	if reads < 3 {
		t.Errorf("only %d valueCtx field selections seen: the scan is blind", reads)
	}
	t.Logf("%d valueCtx field selections, none written", reads)
	if lits != 1 {
		t.Errorf("%d valueCtx literals, want 1 (WithValue's)", lits)
	}
}
