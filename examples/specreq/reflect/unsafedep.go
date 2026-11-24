package reflect

// UNSAFE-DEPENDENT: reflection that exposes addresses or makes Values from
// raw pointers. A semantics without unsafe leaves these stuck; they are here
// so that its authors can see what is left out, and which users depend on it.
//
// Mirrors:
//   - k8s.io/client-go@v0.0.0-20261021054439-569675c57fa3/tools/cache/
//     event_handler_name.go:115-121 (nameForFunction:
//     `runtime.FuncForPC(reflect.ValueOf(f).Pointer())`, a function value's
//     code address to its name; this repository's translation configures it
//     names-only, Code/k8s_io/client_go/tools/cache.toml:52);
//   - Go 1.27.3 fmt/print.go:544-546 (fmtPointer: `uintptr(value.UnsafePointer())`
//     for %p and for a pointer printed below depth 0, so `%v` of a struct
//     with a non-nil pointer field prints an address) and
//     internal/fmtsort/sort.go (pointer map keys ordered by Pointer());
//   - encoding/json/v2 arshal_default.go:56-76 (the cycle check keys on
//     `v.UnsafePointer()`);
//   - github.com/google/go-cmp@v0.7.0 cmp/internal/value/pointer.go:20-23
//     (PointerOf: `unsafe.Pointer(v.Pointer())`, for cycle detection,
//     path.go:366-383, and the order of pointer map keys,
//     internal/value/sort.go:57) and cmp/export.go:18-31
//     (retrieveUnexportedField: `reflect.NewAt(f.Type,
//     unsafe.Pointer(v.UnsafeAddr()+f.Offset)).Elem()`, write access to an
//     unexported field);
//   - google.golang.org/protobuf@v1.36.12 internal/impl/pointer_unsafe.go:
//     47-48 (pointerOfValue: `unsafe.Pointer(v.Pointer())`), :67-78 (Apply:
//     `uintptr(p)+offset`; AsValueOf: `reflect.NewAt(t, p)`): every field
//     accessor of every generated message (message_reflect_field.go), with
//     the offsets of structtags.go. The offset codec itself is in
//     examples/specreq/unsafe/.
//
// To prove (by a semantics with unsafe; stuck otherwise): Pointer of two
// Values is equal iff they are the same pointer (the same function for a
// func), %p prints that address; NewAt(T, base + Offset(field)) is a Value
// of the field, read and written through it.
//
// Needs R3 (doc.go): addresses as integers (Pointer, UnsafePointer,
// UnsafeAddr), NewAt, Offset arithmetic.

import (
	"fmt"
	"reflect"
	"strings"
	"unsafe"
)

func someHandler()  {}
func otherHandler() {}

// funcPC is what event_handler_name.go:116 passes to runtime.FuncForPC (which names the function
// from it: snippets_test.go checks that; Perennial's runtime does not name FuncForPC).
func funcPC(f any) uintptr {
	return reflect.ValueOf(f).Pointer()
}

// retrieveUnexportedField is go-cmp's export.go:18-31 (the addressable case), its
// `unsafe.Pointer(v.UnsafeAddr()+f.Offset)` written with unsafe.Add (the same address; vet's
// unsafeptr check accepts only this form).
func retrieveUnexportedField(v reflect.Value, f reflect.StructField) reflect.Value {
	return reflect.NewAt(f.Type, unsafe.Add(unsafe.Pointer(v.UnsafeAddr()), f.Offset)).Elem()
}

// REQ reflect/unsafe-pointer-identity (UNSAFE-DEPENDENT): Pointer of a function value is the same
// for the same function and differs between two (what FuncForPC names), Pointer of two pointers is equal iff they are the same pointer, %p of
// a pointer is stable and differs between two live allocations, and %v of a struct with a
// non-nil pointer field prints an address.
// Users: client-go tools/cache/event_handler_name.go:116; fmt print.go:544-546; fmtsort;
// encoding/json/v2 arshal_default.go:56-76; go-cmp internal/value/pointer.go:20-23.
// Assumes: nothing.
// Specs: none yet; needs R3: stuck without unsafe (doc.go).
func ReqUnsafePointerIdentity() {
	if funcPC(someHandler) != funcPC(someHandler) || funcPC(someHandler) == funcPC(otherHandler) {
		panic("unsafe-pointer-identity: Pointer of a func is its code address")
	}
	p, q := &Pod2{}, &Pod2{}
	if reflect.ValueOf(p).Pointer() != reflect.ValueOf(p).Pointer() || reflect.ValueOf(p).Pointer() == reflect.ValueOf(q).Pointer() {
		panic("unsafe-pointer-identity: Pointer")
	}
	if fmt.Sprintf("%p", p) != fmt.Sprintf("%p", p) || fmt.Sprintf("%p", p) == fmt.Sprintf("%p", q) {
		panic("unsafe-pointer-identity: %p")
	}
	m := &Member{ID: 1, Next: &Member{ID: 2}}
	if s := fmt.Sprintf("%v", m); !strings.HasPrefix(s, "&{1 {"+" []} 0x") {
		panic("unsafe-pointer-identity: a nested pointer prints its address: " + s)
	}
}

// REQ reflect/unsafe-newat (UNSAFE-DEPENDENT): NewAt of a field's type at the struct's address
// plus the field's Offset is a settable Value of that field, unexported or not: go-cmp's
// Exporter reads it, and protobuf's AsValueOf reads and writes fields that way.
// Users: go-cmp cmp/export.go:18-31; protobuf-go internal/impl/pointer_unsafe.go:47-78,
// message_reflect_field.go (every field accessor).
// Assumes: nothing.
// Specs: none yet; needs R3: stuck without unsafe (doc.go).
func ReqUnsafeNewAt() {
	o := outer{Exported: "e", hidden: "h"}
	v := reflect.ValueOf(&o).Elem()
	f, _ := v.Type().FieldByName("hidden")
	hv := retrieveUnexportedField(v, f)
	if !hv.CanInterface() || hv.Interface().(string) != "h" {
		panic("unsafe-newat: read of an unexported field")
	}
	hv.SetString("h2")
	if o.hidden != "h2" {
		panic("unsafe-newat: write through NewAt")
	}
	cs := &ConfState{Voters: []uint64{4}}
	vf, _ := reflect.TypeOf(*cs).FieldByName("Voters")
	base := unsafe.Pointer(cs)
	lv := reflect.NewAt(vf.Type, unsafe.Add(base, vf.Offset))
	lv.Elem().Set(reflect.Append(lv.Elem(), reflect.ValueOf(uint64(5))))
	if len(cs.Voters) != 2 || cs.Voters[1] != 5 {
		panic("unsafe-newat: protobuf's AsValueOf")
	}
}
