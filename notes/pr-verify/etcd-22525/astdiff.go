package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
)

func decls(path string) map[string]string {
	fs := token.NewFileSet()
	f, err := parser.ParseFile(fs, path, nil, 0)
	if err != nil {
		panic(err)
	}
	m := map[string]string{}
	for _, d := range f.Decls {
		var name string
		switch d := d.(type) {
		case *ast.FuncDecl:
			name = d.Name.Name
			if d.Recv != nil {
				var b bytes.Buffer
				printer.Fprint(&b, fs, d.Recv.List[0].Type)
				name = b.String() + "." + name
			}
		case *ast.GenDecl:
			for _, s := range d.Specs {
				if ts, ok := s.(*ast.TypeSpec); ok {
					name = "type " + ts.Name.Name
				}
			}
			if name == "" {
				continue
			}
		}
		var b bytes.Buffer
		printer.Fprint(&b, token.NewFileSet(), d)
		m[name] = b.String()
	}
	return m
}

func main() {
	a, b := decls(os.Args[1]), decls(os.Args[2])
	for k, v := range b {
		if av, ok := a[k]; !ok {
			fmt.Println("new:", k)
		} else if av != v {
			fmt.Println("changed:", k)
		}
	}
	for k := range a {
		if _, ok := b[k]; !ok {
			fmt.Println("removed:", k)
		}
	}
}
