// Package jsondesc dumps, as JSON, what reflection says about the Go types a program encodes and
// decodes with encoding/json: the input of the encoding/json codec generator
// (models/json/jsongen.py), which derives every type's structure from this dump, never from a
// hand-written list.
//
// The facts are read off package reflect, as encoding/json reads them (Go 1.27.3: the v1 API over
// encoding/json/v2, `encoding/json/v2/fields.go` and `arshal_methods.go`): per type reached from the
// roots, its kind, name, package, String, element type, length, number of methods (an
// interface's), its struct fields (name, exported, embedded, the `json` key of its tag as
// reflect.StructTag.Lookup returns it; the types of exported and of embedded fields are followed),
// which of the methods encoding/json consults it or a pointer to it has (by name), which of
// encoding/json's hook interfaces it or a pointer to it implements (by reflect's Implements), the
// exported method names of a pointer to it, and whether it is encoding/json's RawMessage or
// Number. It decides nothing: the generator's core refuses what is outside its
// subset.
//
// jsongen.py writes a throwaway main package in the program's module that calls Main with the
// roots, each given as its Go expression (as written in the generator's input) and its
// reflect.Type, and reads the JSON Main prints.
package jsondesc

import (
	"encoding"
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"sort"
)

// Root is a root type: its Go expression in the generator's input, and the type.
type Root struct {
	Expr string
	Type reflect.Type
}

// Dump is the generator's input.
type Dump struct {
	Roots []RootRef `json:"roots"`
	Table []Type    `json:"table"`
}

// RootRef is a root: its expression and its type's id in Table.
type RootRef struct {
	Expr string `json:"expr"`
	Type int    `json:"type"`
}

// Type is a type's facts.
type Type struct {
	ID int `json:"id"`
	// Kind: reflect.Kind's String ("int", "struct", "ptr", ...).
	Kind    string `json:"kind"`
	Name    string `json:"name"`
	PkgPath string `json:"pkg_path"`
	// PkgName: the package's name (from String, "pkg.Name"), for a named type of a package.
	PkgName string `json:"pkg_name"`
	String  string `json:"string"`
	Elem    int    `json:"elem"` // slice, array, map, pointer, chan: the element type; else -1
	Key     int    `json:"key"`  // map: the key type; else -1
	Len     int    `json:"len"`  // array: its length
	// NumMethod: reflect's NumMethod (an interface's methods; 0 for `any`).
	NumMethod int     `json:"num_method"`
	Fields    []Field `json:"fields"`
	// Methods: those of JSONMethods the type's method set has; PtrMethods: those a pointer to it
	// has (a superset).
	Methods    []string `json:"methods"`
	PtrMethods []string `json:"ptr_methods"`
	// Implements: per interface of encoding/json's hooks (ImplIfaces: "Marshaler", "Unmarshaler",
	// "TextMarshaler", "TextAppender", "TextUnmarshaler"), whether the type implements it
	// ("value"), only a pointer to it does ("ptr"), or neither (""): reflect's Implements, with the
	// interfaces' real signatures, as encoding/json/v2's `implements` (arshal_methods.go).
	Implements map[string]string `json:"implements"`
	// MethodNames: the exported methods of a pointer to the type (a superset of the type's own),
	// promoted ones included: the generator checks a promoted field's selector is no method.
	MethodNames []string `json:"method_names"`
	// RawMessage: the type is encoding/json's RawMessage (in Go 1.27.3 an alias of
	// encoding/json/jsontext.Value); Number: encoding/json's Number.
	RawMessage bool `json:"raw_message"`
	Number     bool `json:"number"`
}

// Field is a struct field.
type Field struct {
	Name     string `json:"name"`
	Exported bool   `json:"exported"`
	Embedded bool   `json:"embedded"`
	// Tag, HasTag: reflect.StructTag.Lookup("json") of the field's tag.
	Tag    string `json:"tag"`
	HasTag bool   `json:"has_tag"`
	// Type: the field's type (followed for an exported or an embedded field, else -1).
	Type int `json:"type"`
	// TypeString: the field's type's String.
	TypeString string `json:"type_string"`
}

// JSONMethods are the methods through which encoding/json lets a type encode or decode itself
// (Go 1.27.3: Marshaler, Unmarshaler, encoding.TextMarshaler, TextUnmarshaler, TextAppender, and
// encoding/json/v2's MarshalerTo and UnmarshalerFrom; `encoding/json/v2/arshal_methods.go`). The
// dump records any method of these names, whatever its signature.
var JSONMethods = []string{"MarshalJSON", "UnmarshalJSON", "MarshalText", "UnmarshalText",
	"AppendText", "MarshalJSONTo", "UnmarshalJSONFrom"}

// ImplIfaces are the hook interfaces whose implementation the dump records (Go 1.27.3:
// encoding/json.Marshaler and Unmarshaler are aliases of encoding/json/v2's; the text interfaces
// are package encoding's).
var ImplIfaces = map[string]reflect.Type{
	"Marshaler":       reflect.TypeFor[json.Marshaler](),
	"Unmarshaler":     reflect.TypeFor[json.Unmarshaler](),
	"TextMarshaler":   reflect.TypeFor[encoding.TextMarshaler](),
	"TextAppender":    reflect.TypeFor[encoding.TextAppender](),
	"TextUnmarshaler": reflect.TypeFor[encoding.TextUnmarshaler](),
}

func implementsOf(t reflect.Type) map[string]string {
	out := map[string]string{}
	for n, it := range ImplIfaces {
		switch {
		case t.Implements(it):
			out[n] = "value"
		case reflect.PointerTo(t).Implements(it):
			out[n] = "ptr"
		default:
			out[n] = ""
		}
	}
	return out
}

func methodNames(t reflect.Type) []string {
	out := []string{}
	pt := reflect.PointerTo(t)
	for i := 0; i < pt.NumMethod(); i++ {
		out = append(out, pt.Method(i).Name)
	}
	return out
}

var (
	rawMessageT = reflect.TypeFor[json.RawMessage]()
	numberT     = reflect.TypeFor[json.Number]()
)

type dumper struct {
	ids   map[reflect.Type]int
	table []Type
}

func methodsOf(t reflect.Type) []string {
	out := []string{}
	for _, m := range JSONMethods {
		if _, ok := t.MethodByName(m); ok {
			out = append(out, m)
		}
	}
	return out
}

func pkgName(t reflect.Type) string {
	if t.Name() == "" || t.PkgPath() == "" {
		return ""
	}
	s := t.String()
	for i := 0; i < len(s); i++ {
		if s[i] == '.' {
			return s[:i]
		}
	}
	return ""
}

func (d *dumper) id(t reflect.Type) int {
	if id, ok := d.ids[t]; ok {
		return id
	}
	id := len(d.table)
	d.ids[t] = id
	d.table = append(d.table, Type{ID: id})
	e := Type{ID: id, Kind: t.Kind().String(), Name: t.Name(), PkgPath: t.PkgPath(),
		PkgName: pkgName(t), String: t.String(), Elem: -1, Key: -1, Methods: methodsOf(t),
		PtrMethods: methodsOf(reflect.PointerTo(t)), Implements: implementsOf(t),
		MethodNames: methodNames(t), RawMessage: t == rawMessageT, Number: t == numberT}
	if t.Kind() == reflect.Interface {
		e.NumMethod = t.NumMethod()
	}
	switch t.Kind() {
	case reflect.Slice, reflect.Pointer, reflect.Chan:
		e.Elem = d.id(t.Elem())
	case reflect.Array:
		e.Elem = d.id(t.Elem())
		e.Len = t.Len()
	case reflect.Map:
		e.Key = d.id(t.Key())
		e.Elem = d.id(t.Elem())
	case reflect.Struct:
		e.Fields = []Field{}
		for i := 0; i < t.NumField(); i++ {
			f := t.Field(i)
			tag, has := f.Tag.Lookup("json")
			fd := Field{Name: f.Name, Exported: f.IsExported(), Embedded: f.Anonymous, Tag: tag,
				HasTag: has, Type: -1, TypeString: f.Type.String()}
			if fd.Exported || fd.Embedded {
				fd.Type = d.id(f.Type)
			}
			e.Fields = append(e.Fields, fd)
		}
	}
	d.table[id] = e
	return id
}

// Main prints the dump of the roots as JSON on standard output.
func Main(roots []Root) {
	d := &dumper{ids: make(map[reflect.Type]int)}
	out := Dump{Roots: []RootRef{}}
	for _, r := range roots {
		out.Roots = append(out.Roots, RootRef{Expr: r.Expr, Type: d.id(r.Type)})
	}
	out.Table = d.table
	sort.SliceStable(out.Table, func(i, j int) bool { return out.Table[i].ID < out.Table[j].ID })
	b, err := json.MarshalIndent(out, "", " ")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	os.Stdout.Write(append(b, '\n'))
}
