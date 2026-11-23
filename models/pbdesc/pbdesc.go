// Package pbdesc dumps, as JSON, the protobuf schema facts of a set of root message types and of
// every message and enum type they reach, read from the descriptors and Go types that
// protoc-gen-go's generated packages register with google.golang.org/protobuf (protoregistry).
// It is the input of the protobuf codec generator (protobuf/pbgen.py in this module), which
// derives every message's fields from this dump, never from a hand-written list.
//
// These are the same descriptors the real proto.Marshal and proto.Unmarshal run on (the generated
// package's file descriptor, registered by its init), and the same Go struct the generated code
// reads and writes (its exported fields and their `protobuf:"..."` tags). The dump states facts
// only: it decides nothing about the generator's subset (pbgen's core refuses what is outside it).
//
// A program that imports the packages of the root types (for their registration) and calls Main
// with the roots as command-line arguments ("import/path.GoType") prints the dump; pbgen writes
// and runs that program in the target's Go module.
package pbdesc

import (
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"sort"
	"strconv"
	"strings"

	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/reflect/protoregistry"
	"google.golang.org/protobuf/runtime/protoimpl"
	"google.golang.org/protobuf/types/descriptorpb"
)

// Dump is the schema of the roots' closure.
type Dump struct {
	Messages []Message `json:"messages"`
	Enums    []Enum    `json:"enums"`
}

// GoType names a Go type: its package's import path, its package name and its name.
type GoType struct {
	Pkg     string `json:"pkg"`
	PkgName string `json:"pkg_name"`
	Name    string `json:"name"`
}

// Message is a message type's descriptor facts and its Go struct.
type Message struct {
	FullName string `json:"full_name"`
	File     string `json:"file"`
	// Syntax: "proto2", "proto3" or "editions" (the file's).
	Syntax          string `json:"syntax"`
	MapEntry        bool   `json:"map_entry"`
	MessageSet      bool   `json:"message_set"`
	ExtensionRanges int    `json:"extension_ranges"`
	Oneofs          int    `json:"oneofs"`
	// Go: the registered Go type (nil if the message has no Go type registered).
	Go     *GoType `json:"go"`
	Fields []Field `json:"fields"`
	// GoExtra: exported fields of the Go struct that are no descriptor field's and no
	// (non-synthetic) oneof's holder (a struct protoc-gen-go did not generate, or of another API).
	GoExtra []string `json:"go_extra"`
	// OneofDecls: the message's oneofs in declaration order (the descriptor's Oneofs().Get(i)),
	// synthetic ones (proto3 `optional`) included.
	OneofDecls []Oneof `json:"oneof_decls"`
	// GoHidden: struct fields (exported or not) that protobuf-go's struct reader
	// (internal/impl/message.go, structInfo) takes as presence or lazy state: "XXX_presence",
	// "lazyFields", "XXX_lazyUnmarshalInfo" (the opaque and hybrid APIs).
	GoHidden []string `json:"go_hidden"`
	// LegacyOneofFuncs: the Go type has an XXX_OneofFuncs or XXX_OneofWrappers method (APIv1),
	// whose wrappers protobuf-go takes instead of the registered ones (message.go, structInfo).
	LegacyOneofFuncs bool `json:"legacy_oneof_funcs"`
}

// Oneof is a oneof's descriptor facts and its Go holder field.
type Oneof struct {
	Name      string `json:"name"`
	Synthetic bool   `json:"synthetic"`
	// GoField: the Go struct field tagged `protobuf_oneof:"<name>"` ("" if none); GoType: its type
	// (reflect's String); GoKind: its reflect.Kind ("interface" for protoc-gen-go's holders).
	GoField string `json:"go_field"`
	GoType  string `json:"go_type"`
	GoKind  string `json:"go_kind"`
}

// Field is a field's descriptor facts and its Go struct field.
type Field struct {
	Name   string `json:"name"`
	Number int    `json:"number"`
	// Kind: protoreflect.Kind's name ("int32", "sint64", "message", "group", "float", ...).
	Kind string `json:"kind"`
	// Cardinality: "optional", "required" or "repeated".
	Cardinality string `json:"cardinality"`
	Packed      bool   `json:"packed"`
	HasPresence bool   `json:"has_presence"`
	// Oneof: the containing oneof's name ("" if none); Synthetic: it is proto3 `optional`'s.
	Oneof          string `json:"oneof"`
	SyntheticOneof bool   `json:"synthetic_oneof"`
	IsMap          bool   `json:"is_map"`
	IsWeak         bool   `json:"is_weak"`
	Lazy           bool   `json:"lazy"`
	HasDefault     bool   `json:"has_default"`
	EnforceUTF8    bool   `json:"enforce_utf8"`
	// Message, Enum: the full name of a message (group) or enum field's type.
	Message string `json:"message,omitempty"`
	Enum    string `json:"enum,omitempty"`
	// GoField: the exported Go struct field whose protobuf tag has this number ("" if none);
	// GoType: its type (reflect's String), GoElem: the named message or enum type in it.
	GoField string  `json:"go_field"`
	GoType  string  `json:"go_type"`
	GoElem  *GoType `json:"go_elem,omitempty"`
	// GoWrapper: for a field of a non-synthetic oneof, the oneof wrapper type (the registered
	// MessageInfo's OneofWrappers element *W whose one field's protobuf tag has this number, as
	// protobuf-go's structInfo maps them); GoField, GoType and GoElem are then W's field's. Set
	// only if W is a struct of exactly one exported field and *W implements the holder's
	// interface type.
	GoWrapper *GoType `json:"go_wrapper,omitempty"`
}

// Enum is an enum type's descriptor facts and its Go type.
type Enum struct {
	FullName string  `json:"full_name"`
	File     string  `json:"file"`
	Syntax   string  `json:"syntax"`
	Closed   bool    `json:"closed"`
	Go       *GoType `json:"go"`
	// GoKind: the Go type's reflect.Kind ("int32" for protoc-gen-go's enums).
	GoKind string `json:"go_kind"`
}

func goTypeOf(t reflect.Type) *GoType {
	for t.Kind() == reflect.Pointer || t.Kind() == reflect.Slice {
		t = t.Elem()
	}
	if t.Name() == "" || t.PkgPath() == "" {
		return nil
	}
	s := t.String()
	return &GoType{Pkg: t.PkgPath(), PkgName: s[:strings.LastIndex(s, ".")], Name: t.Name()}
}

func syntaxOf(s protoreflect.Syntax) string {
	switch s {
	case protoreflect.Proto2:
		return "proto2"
	case protoreflect.Proto3:
		return "proto3"
	case protoreflect.Editions:
		return "editions"
	}
	return "unknown"
}

// tagNumber is the field number of a `protobuf:"kind,N,..."` tag (-1 if it has none).
func tagNumber(tag string) int {
	parts := strings.Split(tag, ",")
	if len(parts) < 2 {
		return -1
	}
	n, err := strconv.Atoi(parts[1])
	if err != nil {
		return -1
	}
	return n
}

func message(md protoreflect.MessageDescriptor) Message {
	m := Message{
		FullName:        string(md.FullName()),
		File:            md.ParentFile().Path(),
		Syntax:          syntaxOf(md.ParentFile().Syntax()),
		MapEntry:        md.IsMapEntry(),
		ExtensionRanges: md.ExtensionRanges().Len(),
		Oneofs:          md.Oneofs().Len(),
		Fields:          []Field{},
		GoExtra:         []string{},
		OneofDecls:      []Oneof{},
		GoHidden:        []string{},
	}
	if o, ok := md.Options().(*descriptorpb.MessageOptions); ok && o != nil {
		m.MessageSet = o.GetMessageSetWireFormat()
	}
	byNum := map[int]reflect.StructField{}
	holders := map[string]reflect.StructField{} // oneof name -> holder field
	wrappers := map[int]reflect.Type{}          // field number -> wrapper struct type W
	if mt, err := protoregistry.GlobalTypes.FindMessageByName(md.FullName()); err == nil {
		t := reflect.TypeOf(mt.Zero().Interface())
		m.Go = goTypeOf(t)
		if t.Kind() == reflect.Pointer && t.Elem().Kind() == reflect.Struct {
			st := t.Elem()
			for i := 0; i < st.NumField(); i++ {
				sf := st.Field(i)
				switch sf.Name {
				case "XXX_presence", "lazyFields", "XXX_lazyUnmarshalInfo":
					m.GoHidden = append(m.GoHidden, sf.Name)
				}
				if !sf.IsExported() {
					continue
				}
				if on := sf.Tag.Get("protobuf_oneof"); on != "" && sf.Tag.Get("protobuf") == "" {
					if od := md.Oneofs().ByName(protoreflect.Name(on)); od != nil && !od.IsSynthetic() {
						holders[on] = sf
						continue
					}
				}
				n := tagNumber(sf.Tag.Get("protobuf"))
				if n < 0 || md.Fields().ByNumber(protoreflect.FieldNumber(n)) == nil {
					m.GoExtra = append(m.GoExtra, sf.Name)
					continue
				}
				byNum[n] = sf
			}
			for _, name := range []string{"XXX_OneofFuncs", "XXX_OneofWrappers"} {
				if _, ok := t.MethodByName(name); ok {
					m.LegacyOneofFuncs = true
				}
			}
		}
		if mi, ok := mt.(*protoimpl.MessageInfo); ok {
			for _, w := range mi.OneofWrappers {
				wt := reflect.TypeOf(w)
				if wt == nil || wt.Kind() != reflect.Pointer || wt.Elem().Kind() != reflect.Struct ||
					wt.Elem().NumField() != 1 || !wt.Elem().Field(0).IsExported() {
					continue
				}
				if n := tagNumber(wt.Elem().Field(0).Tag.Get("protobuf")); n >= 0 {
					wrappers[n] = wt.Elem()
				}
			}
		}
	}
	for i := 0; i < md.Oneofs().Len(); i++ {
		od := md.Oneofs().Get(i)
		o := Oneof{Name: string(od.Name()), Synthetic: od.IsSynthetic()}
		if sf, ok := holders[o.Name]; ok {
			o.GoField, o.GoType, o.GoKind = sf.Name, sf.Type.String(), sf.Type.Kind().String()
		}
		m.OneofDecls = append(m.OneofDecls, o)
	}
	for i := 0; i < md.Fields().Len(); i++ {
		fd := md.Fields().Get(i)
		f := Field{
			Name:        string(fd.Name()),
			Number:      int(fd.Number()),
			Kind:        fd.Kind().String(),
			Cardinality: fd.Cardinality().String(),
			Packed:      fd.IsPacked(),
			HasPresence: fd.HasPresence(),
			IsMap:       fd.IsMap(),
			IsWeak:      fd.IsWeak(),
			HasDefault:  fd.HasDefault(),
			EnforceUTF8: fd.Kind() == protoreflect.StringKind && enforceUTF8(fd),
		}
		if o := fd.ContainingOneof(); o != nil {
			f.Oneof = string(o.Name())
			f.SyntheticOneof = o.IsSynthetic()
		}
		if o, ok := fd.Options().(*descriptorpb.FieldOptions); ok && o != nil {
			f.Lazy = o.GetLazy() || o.GetUnverifiedLazy()
		}
		if fd.Message() != nil {
			f.Message = string(fd.Message().FullName())
		}
		if fd.Enum() != nil {
			f.Enum = string(fd.Enum().FullName())
		}
		if o := fd.ContainingOneof(); o != nil && !o.IsSynthetic() {
			// a oneof member: its Go field is its wrapper's
			hf, hok := holders[f.Oneof]
			if w, ok := wrappers[f.Number]; ok && hok && hf.Type.Kind() == reflect.Interface &&
				reflect.PointerTo(w).Implements(hf.Type) {
				sf := w.Field(0)
				f.GoWrapper = goTypeOf(w)
				f.GoField = sf.Name
				f.GoType = sf.Type.String()
				if f.Message != "" || f.Enum != "" {
					f.GoElem = goTypeOf(sf.Type)
				}
			}
		} else if sf, ok := byNum[f.Number]; ok {
			f.GoField = sf.Name
			f.GoType = sf.Type.String()
			if f.Message != "" || f.Enum != "" {
				f.GoElem = goTypeOf(sf.Type)
			}
		}
		m.Fields = append(m.Fields, f)
	}
	return m
}

// enforceUTF8 is internal/strs.EnforceUTF8 (protobuf-go v1.36.12, internal/strs/strings.go:19)
// without its legacy flag: proto3 fields are checked, and editions fields by their feature.
func enforceUTF8(fd protoreflect.FieldDescriptor) bool {
	if fd.Syntax() == protoreflect.Editions {
		if e, ok := fd.(interface{ EnforceUTF8() bool }); ok {
			return e.EnforceUTF8()
		}
	}
	return fd.Syntax() == protoreflect.Proto3
}

func enum(ed protoreflect.EnumDescriptor) Enum {
	e := Enum{
		FullName: string(ed.FullName()),
		File:     ed.ParentFile().Path(),
		Syntax:   syntaxOf(ed.ParentFile().Syntax()),
		Closed:   ed.IsClosed(),
	}
	if et, err := protoregistry.GlobalTypes.FindEnumByName(ed.FullName()); err == nil {
		t := reflect.TypeOf(et.New(0))
		e.Go = goTypeOf(t)
		e.GoKind = t.Kind().String()
	}
	return e
}

// rootByGoName finds the registered message whose Go type is *T for name "import/path.T".
func rootByGoName(name string) (protoreflect.MessageDescriptor, error) {
	i := strings.LastIndex(name, ".")
	if i < 0 {
		return nil, fmt.Errorf("root %q: not import/path.GoType", name)
	}
	pkg, tn := name[:i], name[i+1:]
	var found protoreflect.MessageDescriptor
	protoregistry.GlobalTypes.RangeMessages(func(mt protoreflect.MessageType) bool {
		t := reflect.TypeOf(mt.Zero().Interface())
		if t.Kind() == reflect.Pointer && t.Elem().PkgPath() == pkg && t.Elem().Name() == tn {
			found = mt.Descriptor()
			return false
		}
		return true
	})
	if found == nil {
		return nil, fmt.Errorf("root %q: no registered protobuf message has Go type *%s in package %s "+
			"(is the package imported, and generated by protoc-gen-go?)", name, tn, pkg)
	}
	return found, nil
}

// Of is the dump of the roots ("import/path.GoType") and of the message and enum types their
// fields reach (transitively), sorted by full name.
func Of(roots []string) (*Dump, error) {
	var queue []protoreflect.MessageDescriptor
	seen := map[protoreflect.FullName]bool{}
	enums := map[protoreflect.FullName]protoreflect.EnumDescriptor{}
	for _, r := range roots {
		md, err := rootByGoName(r)
		if err != nil {
			return nil, err
		}
		if !seen[md.FullName()] {
			seen[md.FullName()] = true
			queue = append(queue, md)
		}
	}
	d := &Dump{Messages: []Message{}, Enums: []Enum{}}
	for len(queue) > 0 {
		md := queue[0]
		queue = queue[1:]
		d.Messages = append(d.Messages, message(md))
		for i := 0; i < md.Fields().Len(); i++ {
			fd := md.Fields().Get(i)
			if sub := fd.Message(); sub != nil && !seen[sub.FullName()] {
				seen[sub.FullName()] = true
				queue = append(queue, sub)
			}
			if ed := fd.Enum(); ed != nil {
				enums[ed.FullName()] = ed
			}
		}
	}
	for _, ed := range enums {
		d.Enums = append(d.Enums, enum(ed))
	}
	sort.Slice(d.Messages, func(i, j int) bool { return d.Messages[i].FullName < d.Messages[j].FullName })
	sort.Slice(d.Enums, func(i, j int) bool { return d.Enums[i].FullName < d.Enums[j].FullName })
	return d, nil
}

// Main prints the dump of the roots given as command-line arguments, as JSON (exit 1 on an error).
func Main() {
	d, err := Of(os.Args[1:])
	if err != nil {
		fmt.Fprintln(os.Stderr, "pbdesc:", err)
		os.Exit(1)
	}
	b, err := json.MarshalIndent(d, "", " ")
	if err != nil {
		fmt.Fprintln(os.Stderr, "pbdesc:", err)
		os.Exit(1)
	}
	os.Stdout.Write(append(b, '\n'))
}
