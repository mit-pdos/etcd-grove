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
	"strings"
)

func funcs(dir string) map[string]string {
	out := map[string]string{}
	filepath.Walk(dir, func(p string, info os.FileInfo, err error) error {
		if err != nil || info.IsDir() || !strings.HasSuffix(p, ".go") || strings.HasSuffix(p, "_test.go") || strings.Contains(p, "rafttest") || strings.HasSuffix(p, ".pb.go") || strings.Contains(p, "/.git/") {
			return nil
		}
		fs := token.NewFileSet()
		f, err := parser.ParseFile(fs, p, nil, 0)
		if err != nil {
			return nil
		}
		rel, _ := filepath.Rel(dir, filepath.Dir(p))
		for _, d := range f.Decls {
			fd, ok := d.(*ast.FuncDecl)
			if !ok {
				continue
			}
			name := fd.Name.Name
			if fd.Recv != nil {
				var b bytes.Buffer
				printer.Fprint(&b, fs, fd.Recv.List[0].Type)
				name = strings.TrimPrefix(b.String(), "*") + "." + name
			}
			var b bytes.Buffer
			printer.Fprint(&b, fs, fd)
			out[rel+":"+name] = b.String()
		}
		return nil
	})
	return out
}

func main() {
	a, b := funcs(os.Args[1]), funcs(os.Args[2])
	var keys []string
	for k := range b {
		keys = append(keys, k)
	}
	for k := range a {
		if _, ok := b[k]; !ok {
			keys = append(keys, k)
		}
	}
	sort.Strings(keys)
	for _, k := range keys {
		x, okA := a[k]
		y, okB := b[k]
		switch {
		case !okA:
			fmt.Println("new     ", k)
		case !okB:
			fmt.Println("removed ", k)
		case x != y:
			fmt.Println("changed ", k)
		}
	}
}
