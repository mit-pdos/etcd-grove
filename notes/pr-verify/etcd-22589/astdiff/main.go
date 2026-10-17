// astdiff lists the top-level declarations (functions, methods, types, variables) that differ
// between two revisions of the Go files given: `go run . OLDDIR NEWDIR file...`, the files'
// paths relative to both directories. A declaration is compared by its printed AST without
// comments, so formatting and comment changes are ignored.
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
	"sort"
)

func decls(path string) map[string]string {
	out := map[string]string{}
	src, err := os.ReadFile(path)
	if err != nil {
		return out
	}
	fs := token.NewFileSet()
	f, err := parser.ParseFile(fs, path, src, 0)
	if err != nil {
		panic(err)
	}
	for _, d := range f.Decls {
		var buf bytes.Buffer
		printer.Fprint(&buf, fs, d)
		switch d := d.(type) {
		case *ast.FuncDecl:
			name := d.Name.Name
			if d.Recv != nil && len(d.Recv.List) > 0 {
				var r bytes.Buffer
				printer.Fprint(&r, fs, d.Recv.List[0].Type)
				name = r.String() + "." + name
			}
			out["func "+name] = buf.String()
		case *ast.GenDecl:
			for _, s := range d.Specs {
				var b bytes.Buffer
				printer.Fprint(&b, fs, s)
				switch s := s.(type) {
				case *ast.TypeSpec:
					out["type "+s.Name.Name] = b.String()
				case *ast.ValueSpec:
					for _, n := range s.Names {
						out[d.Tok.String()+" "+n.Name] = b.String()
					}
				case *ast.ImportSpec:
					out["import "+s.Path.Value] = b.String()
				}
			}
		}
	}
	return out
}

func main() {
	oldDir, newDir := os.Args[1], os.Args[2]
	for _, file := range os.Args[3:] {
		a, b := decls(filepath.Join(oldDir, file)), decls(filepath.Join(newDir, file))
		var names []string
		for n := range a {
			names = append(names, n)
		}
		for n := range b {
			if _, ok := a[n]; !ok {
				names = append(names, n)
			}
		}
		sort.Strings(names)
		for _, n := range names {
			x, inA := a[n]
			y, inB := b[n]
			switch {
			case !inA:
				fmt.Printf("%s: added %s\n", file, n)
			case !inB:
				fmt.Printf("%s: removed %s\n", file, n)
			case x != y:
				fmt.Printf("%s: changed %s\n", file, n)
			}
		}
	}
}
