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

func funcs(path string) map[string]string {
	m := map[string]string{}
	src, err := os.ReadFile(path)
	if err != nil {
		return m
	}
	fs := token.NewFileSet()
	f, err := parser.ParseFile(fs, path, src, 0)
	if err != nil {
		panic(err)
	}
	for _, d := range f.Decls {
		switch d := d.(type) {
		case *ast.FuncDecl:
			name := d.Name.Name
			if d.Recv != nil {
				var b bytes.Buffer
				printer.Fprint(&b, fs, d.Recv.List[0].Type)
				name = b.String() + "." + name
			}
			var b bytes.Buffer
			printer.Fprint(&b, fs, d)
			m[name] = b.String()
		case *ast.GenDecl:
			for _, s := range d.Specs {
				var b bytes.Buffer
				printer.Fprint(&b, fs, s)
				switch s := s.(type) {
				case *ast.TypeSpec:
					m["type "+s.Name.Name] = b.String()
				case *ast.ValueSpec:
					m["var "+s.Names[0].Name] = b.String()
				}
			}
		}
	}
	return m
}

func main() {
	a, b := funcs(os.Args[1]), funcs(os.Args[2])
	for k, v := range b {
		if w, ok := a[k]; !ok {
			fmt.Println("new", k)
		} else if w != v {
			fmt.Println("changed", k)
		}
	}
	for k := range a {
		if _, ok := b[k]; !ok {
			fmt.Println("removed", k)
		}
	}
}
