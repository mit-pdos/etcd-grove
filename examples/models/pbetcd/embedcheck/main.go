// Command embedcheck: no type embedding a protobuf message declares its own ProtoReflect or Reset
// (#37, the S3 review's item 3; models/protobuf-go/proto/model.go's doc).
//
//	go list -export -json -deps PATTERNS... | go run ./embedcheck
//
// protobuf-go dispatches proto.Marshal, Unmarshal, Size, Clone, Merge and CheckInitialized through
// m.ProtoReflect(), and proto.Reset through m.Reset(); the protobuf model dispatches all of them
// through the PbModel* methods pbgen writes into the message types' packages. A type that embeds a
// message promotes both alike, so the two act on the same embedded message, unless the type
// declares its own ProtoReflect or Reset: then protobuf-go calls that one and the model still
// the embedded message's methods. This command type-checks every package of its input that is
// not only a dependency (`go list -deps`' DepOnly false), against the export data `go list
// -export` built, and reports every named type with an embedded field whose type (or pointer to
// it) is a message (implements protoreflect.ProtoMessage) and that declares a method named
// ProtoReflect or Reset. A package that does not build in the module (go list's Error or
// DepsErrors: a dependency the module does not have) is listed and skipped: nothing built in the
// module uses it. Exits 1 if there is one, 2 on an error.
package main

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"os"
	"path/filepath"
	"sort"
)

type pkg struct {
	ImportPath string
	Dir        string
	Export     string
	GoFiles    []string
	CgoFiles   []string
	DepOnly    bool
	Standard   bool
	ImportMap  map[string]string
	Error      *struct{ Err string }
	DepsErrors []*struct{ Err string }
}

func main() {
	dec := json.NewDecoder(os.Stdin)
	byPath := map[string]*pkg{}
	var targets []*pkg
	for {
		var p pkg
		if err := dec.Decode(&p); err == io.EOF {
			break
		} else if err != nil {
			fmt.Fprintln(os.Stderr, "embedcheck:", err)
			os.Exit(2)
		}
		q := p
		byPath[p.ImportPath] = &q
		if !p.DepOnly && !p.Standard {
			targets = append(targets, &q)
		}
	}
	sort.Slice(targets, func(i, j int) bool { return targets[i].ImportPath < targets[j].ImportPath })
	fset := token.NewFileSet()
	lookup := func(path string) (io.ReadCloser, error) {
		p := byPath[path]
		if p == nil || p.Export == "" {
			return nil, fmt.Errorf("no export data for %s", path)
		}
		return os.Open(p.Export)
	}
	imp := importer.ForCompiler(fset, "gc", lookup).(types.ImporterFrom)
	var msg *types.Interface
	bad, checked, embedding := 0, 0, 0
	var skipped []string
	for _, t := range targets {
		if t.Error != nil || len(t.DepsErrors) > 0 {
			// not buildable in this module (a dependency it does not have): nothing built from
			// this module, so nothing translated from it, uses the package
			skipped = append(skipped, t.ImportPath)
			continue
		}
		if len(t.CgoFiles) > 0 {
			fmt.Fprintf(os.Stderr, "embedcheck: %s has cgo files (not checked)\n", t.ImportPath)
			os.Exit(2)
		}
		var files []*ast.File
		for _, f := range t.GoFiles {
			af, err := parser.ParseFile(fset, filepath.Join(t.Dir, f), nil, parser.SkipObjectResolution)
			if err != nil {
				fmt.Fprintln(os.Stderr, "embedcheck:", err)
				os.Exit(2)
			}
			files = append(files, af)
		}
		conf := types.Config{Importer: mapped{imp, t.ImportMap}, Error: func(error) {}}
		tp, err := conf.Check(t.ImportPath, fset, files, nil)
		if err != nil {
			fmt.Fprintf(os.Stderr, "embedcheck: %s: %v\n", t.ImportPath, err)
			os.Exit(2)
		}
		checked++
		if msg == nil {
			pr, err := imp.ImportFrom("google.golang.org/protobuf/reflect/protoreflect", t.Dir, 0)
			if err == nil {
				msg = pr.Scope().Lookup("ProtoMessage").Type().Underlying().(*types.Interface)
			}
		}
		if msg == nil {
			continue // nothing in reach declares a message so far
		}
		scope := tp.Scope()
		for _, name := range scope.Names() {
			tn, ok := scope.Lookup(name).(*types.TypeName)
			if !ok {
				continue
			}
			named, ok := tn.Type().(*types.Named)
			if !ok {
				continue
			}
			st, ok := named.Underlying().(*types.Struct)
			if !ok {
				continue
			}
			var emb []string
			for i := 0; i < st.NumFields(); i++ {
				f := st.Field(i)
				if f.Embedded() && (types.Implements(f.Type(), msg) || types.Implements(types.NewPointer(f.Type()), msg)) {
					emb = append(emb, f.Type().String())
				}
			}
			if len(emb) == 0 {
				continue
			}
			embedding++
			for i := 0; i < named.NumMethods(); i++ {
				if m := named.Method(i); m.Name() == "ProtoReflect" || m.Name() == "Reset" {
					fmt.Printf("%s: %s.%s embeds %v and declares %s\n", fset.Position(m.Pos()), t.ImportPath, name, emb, m.Name())
					bad++
				}
			}
		}
	}
	fmt.Printf("embedcheck: %d packages, %d types embedding a message, %d declaring ProtoReflect or Reset\n", checked, embedding, bad)
	if len(skipped) > 0 {
		fmt.Printf("embedcheck: %d packages not buildable in the module, not checked: %v\n", len(skipped), skipped)
	}
	if bad > 0 {
		os.Exit(1)
	}
}

// mapped resolves a package's import paths through its ImportMap (vendoring, test variants).
type mapped struct {
	imp types.ImporterFrom
	m   map[string]string
}

func (x mapped) Import(path string) (*types.Package, error) { return x.ImportFrom(path, "", 0) }

func (x mapped) ImportFrom(path, dir string, mode types.ImportMode) (*types.Package, error) {
	if p, ok := x.m[path]; ok {
		path = p
	}
	return x.imp.ImportFrom(path, dir, mode)
}
