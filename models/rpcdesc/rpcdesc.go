// Package rpcdesc dumps, as JSON, what reflection says about a program's net/rpc receivers and
// the types their methods take: the input of the net/rpc codec generator
// (models/net/rpc/rpcgen.py), which derives the methods and every type's structure from this
// dump, never from a hand-written list.
//
// The facts are read off package reflect, as net/rpc and encoding/gob read them: per receiver,
// its type's String and (through a pointer) Name, the methods net/rpc's suitableMethods registers
// for its type (the same tests, copied from net/rpc/server.go, Go 1.27.3) and how many it
// registers for a pointer to it (Register's hint); per type reached from the methods' argument
// and reply types and from the listed extra types, its kind, name, package, String, element and
// key types, struct fields (name, exported, embedded; the types of exported fields are followed),
// and whether the type or a pointer to it implements gob's GobEncoder, encoding's
// BinaryMarshaler or TextMarshaler (gob then uses those methods). It decides nothing: the
// generator's core refuses what is outside its subset.
//
// rpcgen.py writes a throwaway main package in the program's module that calls Main with the
// roots, each given as its Go expression (as written in the generator's input) and its
// reflect.Type, and reads the JSON Main prints.
package rpcdesc

import (
	"encoding"
	"encoding/gob"
	"encoding/json"
	"fmt"
	"go/token"
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
	Receivers []Receiver `json:"receivers"`
	Types     []RootRef  `json:"types"`
	Table     []Type     `json:"table"`
}

// RootRef is a listed extra type.
type RootRef struct {
	Expr string `json:"expr"`
	Type int    `json:"type"`
}

// Receiver is a receiver type's facts.
type Receiver struct {
	Expr string `json:"expr"`
	Type int    `json:"type"`
	// Name: reflect.Indirect(v).Type().Name() for a (non-nil) value v of the type.
	Name string `json:"name"`
	// String: the type's String (reflect.TypeOf(v).String()).
	String string `json:"string"`
	// Pointer: the type is a pointer type.
	Pointer bool `json:"pointer"`
	// Methods: the methods suitableMethods(typ) registers, by name.
	Methods []Method `json:"methods"`
	// PtrMethods: how many suitableMethods(reflect.PointerTo(typ)) registers.
	PtrMethods int `json:"ptr_methods"`
}

// Method is a method suitableMethods registers: its name, argument type (a pointer or not) and
// reply type (a pointer).
type Method struct {
	Name  string `json:"name"`
	Arg   int    `json:"arg"`
	Reply int    `json:"reply"`
}

// Type is a type's facts.
type Type struct {
	ID int `json:"id"`
	// Kind: reflect.Kind's String ("int", "struct", "ptr", ...).
	Kind    string `json:"kind"`
	Name    string `json:"name"`
	PkgPath string `json:"pkg_path"`
	// PkgName: the package's name (from String, "pkg.Name"), for a named type of a package.
	PkgName string  `json:"pkg_name"`
	String  string  `json:"string"`
	Elem    int     `json:"elem"` // slice, array, map, pointer, chan: the element type; else -1
	Key     int     `json:"key"`  // map: the key type; else -1
	Len     int     `json:"len"`  // array: its length
	Fields  []Field `json:"fields"`
	// The interfaces gob consults (for the type or a pointer to it).
	GobEncoder        bool `json:"gob_encoder"`
	GobDecoder        bool `json:"gob_decoder"`
	BinaryMarshaler   bool `json:"binary_marshaler"`
	BinaryUnmarshaler bool `json:"binary_unmarshaler"`
	TextMarshaler     bool `json:"text_marshaler"`
	TextUnmarshaler   bool `json:"text_unmarshaler"`
}

// Field is a struct field: its name, whether it is exported and embedded, and its type (-1 for
// an unexported field: not followed, gob ignores it).
type Field struct {
	Name     string `json:"name"`
	Exported bool   `json:"exported"`
	Embedded bool   `json:"embedded"`
	Type     int    `json:"type"`
	// TypeString: the field's type's String (for an unexported field, whose type is not
	// followed).
	TypeString string `json:"type_string"`
}

// Copied from net/rpc/server.go (Go 1.27.3).
var typeOfError = reflect.TypeFor[error]()

// isExportedOrBuiltinType is net/rpc's (server.go).
func isExportedOrBuiltinType(t reflect.Type) bool {
	for t.Kind() == reflect.Pointer {
		t = t.Elem()
	}
	// PkgPath will be non-empty even for an exported type,
	// so we need to check the type name as well.
	return token.IsExported(t.Name()) || t.PkgPath() == ""
}

// suitableMethods is net/rpc's (server.go), returning the methods' reflect.Method.
func suitableMethods(typ reflect.Type) map[string]reflect.Method {
	methods := make(map[string]reflect.Method)
	for m := 0; m < typ.NumMethod(); m++ {
		method := typ.Method(m)
		mtype := method.Type
		mname := method.Name
		// Method must be exported.
		if !method.IsExported() {
			continue
		}
		// Method needs three ins: receiver, *args, *reply.
		if mtype.NumIn() != 3 {
			continue
		}
		// First arg need not be a pointer.
		argType := mtype.In(1)
		if !isExportedOrBuiltinType(argType) {
			continue
		}
		// Second arg must be a pointer.
		replyType := mtype.In(2)
		if replyType.Kind() != reflect.Pointer {
			continue
		}
		// Reply type must be exported.
		if !isExportedOrBuiltinType(replyType) {
			continue
		}
		// Method needs one out.
		if mtype.NumOut() != 1 {
			continue
		}
		// The return type of the method must be error.
		if returnType := mtype.Out(0); returnType != typeOfError {
			continue
		}
		methods[mname] = method
	}
	return methods
}

type dumper struct {
	ids   map[reflect.Type]int
	table []Type
}

func implements(t reflect.Type, iface reflect.Type) bool {
	return t.Implements(iface) || reflect.PointerTo(t).Implements(iface)
}

var (
	gobEncoderT        = reflect.TypeFor[gob.GobEncoder]()
	gobDecoderT        = reflect.TypeFor[gob.GobDecoder]()
	binaryMarshalerT   = reflect.TypeFor[encoding.BinaryMarshaler]()
	binaryUnmarshalerT = reflect.TypeFor[encoding.BinaryUnmarshaler]()
	textMarshalerT     = reflect.TypeFor[encoding.TextMarshaler]()
	textUnmarshalerT   = reflect.TypeFor[encoding.TextUnmarshaler]()
)

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
		PkgName: pkgName(t), String: t.String(), Elem: -1, Key: -1,
		GobEncoder: implements(t, gobEncoderT), GobDecoder: implements(t, gobDecoderT),
		BinaryMarshaler: implements(t, binaryMarshalerT), BinaryUnmarshaler: implements(t, binaryUnmarshalerT),
		TextMarshaler: implements(t, textMarshalerT), TextUnmarshaler: implements(t, textUnmarshalerT)}
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
			fd := Field{Name: f.Name, Exported: f.IsExported(), Embedded: f.Anonymous, Type: -1,
				TypeString: f.Type.String()}
			if fd.Exported {
				fd.Type = d.id(f.Type)
			}
			e.Fields = append(e.Fields, fd)
		}
	}
	d.table[id] = e
	return id
}

// Main prints the dump of the receivers and the extra types as JSON on standard output.
func Main(receivers []Root, types []Root) {
	d := &dumper{ids: make(map[reflect.Type]int)}
	out := Dump{Receivers: []Receiver{}, Types: []RootRef{}}
	for _, r := range receivers {
		t := r.Type
		ind := t
		if ind.Kind() == reflect.Pointer {
			ind = ind.Elem()
		}
		rc := Receiver{Expr: r.Expr, Type: d.id(t), Name: ind.Name(), String: t.String(),
			Pointer: t.Kind() == reflect.Pointer, Methods: []Method{}}
		ms := suitableMethods(t)
		names := make([]string, 0, len(ms))
		for n := range ms {
			names = append(names, n)
		}
		sort.Strings(names)
		for _, n := range names {
			mt := ms[n].Type
			rc.Methods = append(rc.Methods, Method{Name: n, Arg: d.id(mt.In(1)), Reply: d.id(mt.In(2))})
		}
		rc.PtrMethods = len(suitableMethods(reflect.PointerTo(t)))
		out.Receivers = append(out.Receivers, rc)
	}
	for _, r := range types {
		out.Types = append(out.Types, RootRef{Expr: r.Expr, Type: d.id(r.Type)})
	}
	out.Table = d.table
	b, err := json.MarshalIndent(out, "", " ")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	os.Stdout.Write(append(b, '\n'))
}
