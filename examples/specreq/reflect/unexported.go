package reflect

// Values read through unexported fields: readable by the typed getters, but
// Interface and Set panic.
//
// Mirrors Go 1.27.3 reflect/value.go (Value.Interface -> valueInterface:
// panics "reflect.Value.Interface: cannot return value obtained from
// unexported field or method" when the value's flagRO is set; Set ->
// mustBeAssignable: panics "reflect: reflect.Value.Set using value obtained
// using unexported field"; CanInterface and CanSet report both), and the
// code that depends on the distinction: fmt/print.go:758 (printValue calls a
// nested value's methods only if CanInterface, and reads unexported fields
// by the typed getters, fmtprint.go); net/http transport.go:452-458
// (`Field(0).CanInterface()` before Interface, on x/net/http2's struct);
// net/http transfer.go:1150 (unwrapNopCloser's Field(0) is io.nopCloser's
// embedded exported Reader, so Interface succeeds: httpunwrap.go);
// encoding/json/v2 fields.go (unexported fields are skipped, jsonwalk.go);
// encoding/binary (a Set through an unexported field panics, binaryrw.go);
// go-cmp's validator ("cannot handle unexported field", cmpwalk.go); and
// reflect.DeepEqual, which compares unexported fields (deepequal.go).
//
// To prove: the flag is tracked through Field (a field of an unexported
// field is read-only too, and so is an exported field of a value read
// through an unexported one), the getters succeed, CanInterface/CanSet are
// false, and the Must* functions panic.
//
// Needs R2 (Field, the read-only flag, CanInterface, CanSet, Interface, Set,
// String/Int getters) and R1 (StructField.IsExported, PkgPath).

import "reflect"

type inner struct{ Name string }

type outer struct {
	Exported string
	hidden   string
	in       inner
}

// REQ reflect/unexported: an unexported field reads by its getter but is neither interfaceable
// nor settable, an exported field of an unexported field is read-only too, and an exported
// field of an addressable struct is settable.
// Users: fmt print.go:758; net/http transport.go:452-458, transfer.go:1150; encoding/json/v2
// fields.go; encoding/binary binary.go:862; go-cmp's validator; reflect.DeepEqual.
// Assumes: nothing.
// Specs: none yet; needs R1 and R2 (doc.go).
func ReqUnexported() {
	o := outer{Exported: "e", hidden: "h", in: inner{Name: "n"}}
	v := reflect.ValueOf(&o).Elem()
	h := v.Field(1)
	if h.String() != "h" || h.CanInterface() || h.CanSet() {
		panic("unexported: an unexported field reads but is read-only")
	}
	if n := v.Field(2).Field(0); n.String() != "n" || n.CanInterface() || n.CanSet() {
		panic("unexported: read-only is inherited through Field")
	}
	e := v.Field(0)
	if !e.CanInterface() || !e.CanSet() || e.Interface().(string) != "e" {
		panic("unexported: an exported field")
	}
	e.SetString("e2")
	if o.Exported != "e2" {
		panic("unexported: Set of an exported field writes the struct")
	}
	t := v.Type()
	if t.Field(0).IsExported() == t.Field(1).IsExported() || t.Field(1).PkgPath != pkgPath || t.Field(0).PkgPath != "" {
		panic("unexported: StructField's IsExported and PkgPath")
	}
}

// REQ reflect/unexported (panics): Interface of an unexported field panics
// "reflect.Value.Interface: cannot return value obtained from unexported field or method".
// Specs: none yet.
func MustPanicInterfaceUnexported() any {
	return reflect.ValueOf(outer{hidden: "h"}).Field(1).Interface()
}

// REQ reflect/unexported (panics): SetString of an unexported field of an addressable struct
// panics "reflect: reflect.Value.SetString using value obtained using unexported field".
// Specs: none yet.
func MustPanicSetUnexported() {
	o := outer{}
	reflect.ValueOf(&o).Elem().Field(1).SetString("x")
}
