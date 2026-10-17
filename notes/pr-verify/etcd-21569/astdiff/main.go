// astdiff: lists the functions of the given Go files that differ (body or signature, comments
// ignored) between two checkouts. usage: astdiff OLDROOT NEWROOT file.go...
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
)

func funcs(path string) map[string]string {
	m := map[string]string{}
	fs := token.NewFileSet()
	f, err := parser.ParseFile(fs, path, nil, 0)
	if err != nil {
		return m
	}
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok {
			continue
		}
		name := fd.Name.Name
		if fd.Recv != nil && len(fd.Recv.List) > 0 {
			var b bytes.Buffer
			printer.Fprint(&b, fs, fd.Recv.List[0].Type)
			name = "(" + b.String() + ")." + name
		}
		var b bytes.Buffer
		printer.Fprint(&b, fs, fd)
		m[name] = b.String()
	}
	return m
}

func main() {
	oldRoot, newRoot := os.Args[1], os.Args[2]
	for _, f := range os.Args[3:] {
		o, n := funcs(filepath.Join(oldRoot, f)), funcs(filepath.Join(newRoot, f))
		for k, v := range n {
			if ov, ok := o[k]; !ok {
				fmt.Printf("%s: %s: added\n", f, k)
			} else if ov != v {
				fmt.Printf("%s: %s: changed\n", f, k)
			}
		}
		for k := range o {
			if _, ok := n[k]; !ok {
				fmt.Printf("%s: %s: removed\n", f, k)
			}
		}
	}
}
