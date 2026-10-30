// Command k8s-callgraph writes the call graph reachable from a root function of a Go package, for
// etc/k8s-worklist.py (the DaemonSet example's worklist, notes/k8s-daemonset-goose.md): VTA
// (golang.org/x/tools/go/callgraph/vta) over RTA's reachable functions and call graph, with every
// package initializer also an RTA root (package variables holding functions, such as
// legacyregistry.MustRegister, are set there), then the functions reachable from the root alone.
// One line per function, then one per edge, fields tab-separated:
//
//	F <id> <package> <receiver type> <name> <id of the enclosing function, or -> <file:line> <lines> <synthetic, or -> <ssa name>
//	E <caller id> <callee id>
//
// Node 0 is the root. A closure is its own node; its <name> is its enclosing function's.
//
// Usage: k8s-callgraph MODULE-DIR PACKAGE ROOT-FUNCTION (go run . ../../examples/k8sdaemonset ./dsmain Main)
package main

import (
	"fmt"
	"go/types"
	"os"
	"strings"

	"golang.org/x/tools/go/callgraph/rta"
	"golang.org/x/tools/go/callgraph/vta"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

func recvName(f *ssa.Function) string {
	sig := f.Signature
	if sig.Recv() == nil {
		return ""
	}
	t := sig.Recv().Type()
	if p, ok := t.(*types.Pointer); ok {
		t = p.Elem()
	}
	if n, ok := types.Unalias(t).(*types.Named); ok {
		return n.Obj().Name()
	}
	return "?" + t.String()
}

func main() {
	if len(os.Args) != 4 {
		fmt.Fprintln(os.Stderr, "usage: k8s-callgraph MODULE-DIR PACKAGE ROOT-FUNCTION")
		os.Exit(2)
	}
	dir, pkgPath, root := os.Args[1], os.Args[2], os.Args[3]
	cfg := &packages.Config{Mode: packages.LoadAllSyntax, Dir: dir}
	pkgs, err := packages.Load(cfg, pkgPath)
	if err != nil {
		panic(err)
	}
	if packages.PrintErrors(pkgs) > 0 {
		os.Exit(1)
	}
	if len(pkgs) != 1 {
		panic("expected one package")
	}
	prog, spkgs := ssautil.AllPackages(pkgs, ssa.InstantiateGenerics)
	prog.Build()
	r := spkgs[0].Func(root)
	if r == nil {
		panic("no function " + root + " in " + pkgPath)
	}
	roots := []*ssa.Function{r}
	for _, p := range prog.AllPackages() {
		if f := p.Func("init"); f != nil {
			roots = append(roots, f)
		}
	}
	res := rta.Analyze(roots, true)
	funcs := map[*ssa.Function]bool{}
	for f := range res.Reachable {
		funcs[f] = true
	}
	cg := vta.CallGraph(funcs, res.CallGraph)
	cg.DeleteSyntheticNodes()

	ids := map[*ssa.Function]int{}
	var order []*ssa.Function
	id := func(f *ssa.Function) int {
		if i, ok := ids[f]; ok {
			return i
		}
		ids[f] = len(order)
		order = append(order, f)
		return ids[f]
	}
	seen := map[*ssa.Function]bool{r: true}
	q := []*ssa.Function{r}
	var edges [][2]int
	for len(q) > 0 {
		f := q[0]
		q = q[1:]
		id(f)
		n := cg.Nodes[f]
		if n == nil {
			continue
		}
		done := map[*ssa.Function]bool{}
		for _, e := range n.Out {
			g := e.Callee.Func
			if done[g] {
				continue
			}
			done[g] = true
			edges = append(edges, [2]int{id(f), id(g)})
			if !seen[g] {
				seen[g] = true
				q = append(q, g)
			}
		}
	}
	fset := prog.Fset
	for i := 0; i < len(order); i++ { // (id may append enclosing functions)
		f := order[i]
		g := f
		if f.Origin() != nil {
			g = f.Origin()
		}
		pkg := ""
		if g.Pkg != nil {
			pkg = g.Pkg.Pkg.Path()
		} else if g.Object() != nil && g.Object().Pkg() != nil {
			pkg = g.Object().Pkg().Path()
		}
		parent := "-"
		if f.Parent() != nil {
			parent = fmt.Sprint(id(f.Parent()))
		}
		pos, lines := "-", 0
		if f.Syntax() != nil {
			p, e := fset.Position(f.Syntax().Pos()), fset.Position(f.Syntax().End())
			pos = fmt.Sprintf("%s:%d", p.Filename, p.Line)
			lines = e.Line - p.Line + 1
		}
		syn := f.Synthetic
		if syn == "" {
			syn = "-"
		}
		name := g.Name()
		if i := strings.Index(name, "$"); i >= 0 {
			name = name[:i]
		}
		fmt.Printf("F\t%d\t%s\t%s\t%s\t%s\t%s\t%d\t%s\t%s\n", i, pkg, recvName(g), name, parent, pos, lines,
			strings.ReplaceAll(syn, "\t", " "), strings.ReplaceAll(f.String(), "\t", " "))
	}
	for _, e := range edges {
		fmt.Printf("E\t%d\t%d\n", e[0], e[1])
	}
}
