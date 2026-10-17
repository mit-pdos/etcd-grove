package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"strings"
)

func decls(dir string) map[string]string {
	m := map[string]string{}
	fs := token.NewFileSet()
	pkgs, err := parser.ParseDir(fs, dir, func(fi os.FileInfo) bool { return !strings.HasSuffix(fi.Name(), "_test.go") }, 0)
	if err != nil { panic(err) }
	for _, p := range pkgs {
		for _, f := range p.Files {
			for _, d := range f.Decls {
				var name string
				switch d := d.(type) {
				case *ast.FuncDecl:
					name = d.Name.Name
					if d.Recv != nil {
						var b bytes.Buffer
						printer.Fprint(&b, fs, d.Recv.List[0].Type)
						name = strings.TrimPrefix(b.String(), "*") + "." + name
					}
				case *ast.GenDecl:
					for _, s := range d.Specs {
						if ts, ok := s.(*ast.TypeSpec); ok { name += "type " + ts.Name.Name }
						if vs, ok := s.(*ast.ValueSpec); ok { name += "var " + vs.Names[0].Name }
					}
				}
				var b bytes.Buffer
				printer.Fprint(&b, token.NewFileSet(), d)
				m[name] = b.String()
			}
		}
	}
	return m
}

func main() {
	a, b := decls(os.Args[1]), decls(os.Args[2])
	for k, v := range a {
		if w, ok := b[k]; !ok { fmt.Println("removed", k) } else if v != w { fmt.Println("changed", k) }
	}
	for k := range b { if _, ok := a[k]; !ok { fmt.Println("added", k) } }
}
