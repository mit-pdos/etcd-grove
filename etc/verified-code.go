// Lists the Go functions of the given source trees, for etc/verified-code.py.
//
//	go run etc/verified-code.go DIR...
//
// One JSON object per line for each function or method declared outside a
// `_test.go` file:
//
//	{"pkg": import path, "file": path relative to DIR, "recv": receiver type ("" for a
//	 function), "name", "line", "end": the lines of `func` and the closing brace,
//	 "sloc": the lines in that range holding code (not blank, not only comments),
//	 "generated": the file says it is generated ("Code generated ... DO NOT EDIT.")}
//
// The import path is the module path of the nearest `go.mod` plus the directory.
// `testdata` and `vendor` directories, hidden directories, and files the default
// build excludes (build constraints, such as raft's `with_tla`) are skipped.
package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/scanner"
	"go/token"
	"os"
	"path/filepath"
	"strings"
)

type fn struct {
	Pkg       string `json:"pkg"`
	File      string `json:"file"`
	Recv      string `json:"recv"`
	Name      string `json:"name"`
	Line      int    `json:"line"`
	End       int    `json:"end"`
	Sloc      int    `json:"sloc"`
	Generated bool   `json:"generated"`
}

// modulePath reads the module path of the go.mod in dir, if any.
func modulePath(dir string) (string, bool) {
	f, err := os.Open(filepath.Join(dir, "go.mod"))
	if err != nil {
		return "", false
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		if m, ok := strings.CutPrefix(strings.TrimSpace(sc.Text()), "module "); ok {
			return strings.Trim(strings.TrimSpace(m), `"`), true
		}
	}
	return "", false
}

func recvName(e ast.Expr) string {
	for {
		switch t := e.(type) {
		case *ast.StarExpr:
			e = t.X
		case *ast.ParenExpr:
			e = t.X
		case *ast.IndexExpr:
			e = t.X
		case *ast.IndexListExpr:
			e = t.X
		case *ast.Ident:
			return t.Name
		default:
			return ""
		}
	}
}

// codeLines is the set of lines of src holding a token other than a comment.
func codeLines(fset *token.FileSet, src []byte) map[int]bool {
	lines := map[int]bool{}
	file := fset.AddFile("", fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, nil, 0) // mode 0: comments are skipped
	for {
		pos, tok, lit := s.Scan()
		if tok == token.EOF {
			break
		}
		if tok == token.SEMICOLON && lit == "\n" {
			continue // an inserted semicolon is not code
		}
		l := file.Line(pos)
		lines[l] = true
		for i := 0; i < strings.Count(lit, "\n"); i++ { // raw strings span lines
			lines[l+i+1] = true
		}
	}
	return lines
}

func walk(root string, out *json.Encoder) error {
	type mod struct{ dir, path string }
	var mods []mod // innermost last
	return filepath.WalkDir(root, func(p string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			n := d.Name()
			if p != root && (n == "testdata" || n == "vendor" || strings.HasPrefix(n, ".")) {
				return filepath.SkipDir
			}
			for len(mods) > 0 && !strings.HasPrefix(p+"/", mods[len(mods)-1].dir+"/") {
				mods = mods[:len(mods)-1]
			}
			if m, ok := modulePath(p); ok {
				mods = append(mods, mod{p, m})
			}
			return nil
		}
		if !strings.HasSuffix(p, ".go") || strings.HasSuffix(p, "_test.go") || len(mods) == 0 {
			return nil
		}
		m := mods[len(mods)-1]
		if ok, err := build.Default.MatchFile(filepath.Dir(p), filepath.Base(p)); err != nil || !ok {
			return nil // not in the default build (build constraints)
		}
		src, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, p, src, parser.ParseComments)
		if err != nil {
			fmt.Fprintf(os.Stderr, "verified-code: skipping %s: %v\n", p, err)
			return nil
		}
		code := codeLines(token.NewFileSet(), src)
		rel, _ := filepath.Rel(root, p)
		pkg := m.path
		if d, _ := filepath.Rel(m.dir, filepath.Dir(p)); d != "." {
			pkg += "/" + filepath.ToSlash(d)
		}
		gen := ast.IsGenerated(f)
		for _, decl := range f.Decls {
			fd, ok := decl.(*ast.FuncDecl)
			if !ok {
				continue
			}
			r := ""
			if fd.Recv != nil && len(fd.Recv.List) > 0 {
				r = recvName(fd.Recv.List[0].Type)
			}
			l0, l1 := fset.Position(fd.Pos()).Line, fset.Position(fd.End()).Line
			n := 0
			for l := l0; l <= l1; l++ {
				if code[l] {
					n++
				}
			}
			if err := out.Encode(fn{pkg, filepath.ToSlash(rel), r, fd.Name.Name, l0, l1, n, gen}); err != nil {
				return err
			}
		}
		return nil
	})
}

func main() {
	out := json.NewEncoder(os.Stdout)
	for _, dir := range os.Args[1:] {
		if err := walk(dir, out); err != nil {
			fmt.Fprintln(os.Stderr, "verified-code:", err)
			os.Exit(1)
		}
	}
}
