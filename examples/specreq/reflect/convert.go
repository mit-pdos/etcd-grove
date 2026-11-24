package reflect

// Value.Convert between named types and their underlying types: protobuf's
// converters and enums, k8s's unstructured map keys.
//
// Mirrors:
//   - google.golang.org/protobuf@v1.36.12 internal/impl/convert.go:145-200,
//     380-395 (the scalar and enum converters: PBValueOf panics "invalid type:
//     got %v, want %v" unless `v.Type() == c.goType`, then reads `v.Int()`
//     or `v.Bool()`; GoValueOf is `reflect.ValueOf(int32(v.Int())).Convert(c.goType)`,
//     `reflect.ValueOf(v.Enum()).Convert(c.goType)`), and enum.go:19
//     (EnumInfo.New: `reflect.ValueOf(n).Convert(t.GoReflectType).Interface().(protoreflect.Enum)`):
//     every enum field of a generated message (raftpb's MessageType,
//     EntryType, ConfChangeType; etcdserverpb's Compare_CompareTarget, ...)
//     goes through them on ProtoReflect, proto.Clone, proto.Equal and the
//     text and JSON formats;
//   - k8s.io/apimachinery@v0.0.0-20261021173754-0b7d352f711c/pkg/runtime/
//     converter.go:731-743 (mapToUnstructured: `st.Key().AssignableTo(dt.Key())`
//     else `ConvertibleTo`, `dv.SetMapIndex(key.Convert(dt.Key()), value)`);
//   - Go 1.27.3 net/http/internal/http2/errors.go:95-118 (StreamError.As:
//     ConvertibleTo, Convert of a field).
//
// Go's panic: Convert to a type the value is not convertible to panics
// "reflect.Value.Convert: value of type string cannot be converted to type
// reflect.EntryType".
//
// To prove: the converters round-trip each enum value (Go value -> number
// -> Go value of the same named type, String method included); PBValueOf
// never panics on the field's own Go type and panics on another (the
// "invalid type" case is unreachable from generated code, where the Go type
// is the field's); a named string key converts to the map's string key.
//
// Needs R1 (type identity, Kind, ConvertibleTo, AssignableTo, Key) and R2
// (ValueOf, Int, Convert between a named integer type and its underlying
// type, Interface of the result with its method set, SetMapIndex).

import (
	"fmt"
	"reflect"
)

// EntryType is a generated enum (raftpb.EntryType).
type EntryType int32

const (
	EntryNormal     EntryType = 0
	EntryConfChange EntryType = 1
)

func (x EntryType) String() string {
	switch x {
	case EntryNormal:
		return "EntryNormal"
	case EntryConfChange:
		return "EntryConfChange"
	}
	return fmt.Sprint(int32(x))
}

// Number is protoreflect.EnumNumber.
type Number int32

// Enum stands for protoreflect.Enum.
type Enum interface{ String() string }

type enumConverter struct{ goType reflect.Type }

// PBValueOf is convert.go:383-388: the number of a Go enum value.
func (c *enumConverter) PBValueOf(v reflect.Value) Number {
	if v.Type() != c.goType {
		panic(fmt.Sprintf("invalid type: got %v, want %v", v.Type(), c.goType))
	}
	return Number(v.Int())
}

// GoValueOf is convert.go:390-392.
func (c *enumConverter) GoValueOf(n Number) reflect.Value {
	return reflect.ValueOf(n).Convert(c.goType)
}

// newEnum is EnumInfo.New (enum.go:19).
func newEnum(goType reflect.Type, n Number) Enum {
	return reflect.ValueOf(n).Convert(goType).Interface().(Enum)
}

type NamedKey string

// REQ reflect/convert: the enum converter maps EntryConfChange to 1 and back to the named
// EntryType (whose String method then runs), EnumInfo.New gives an Enum of the Go type, a
// named string map key converts to string for the unstructured map, and ConvertibleTo agrees
// with what Convert accepts.
// Users: protobuf-go internal/impl/convert.go:145-200,380-395, enum.go:19 (every enum field);
// apimachinery runtime/converter.go:731-743; net/http internal/http2/errors.go:95-118.
// Assumes: nothing.
// Specs: none yet; needs R1 and R2 (Convert) (doc.go).
func ReqConvert() {
	c := &enumConverter{goType: reflect.TypeOf(EntryNormal)}
	n := c.PBValueOf(reflect.ValueOf(EntryConfChange))
	if n != 1 {
		panic("convert: enum number")
	}
	back := c.GoValueOf(n)
	if back.Type() != c.goType || back.Interface().(EntryType) != EntryConfChange {
		panic("convert: enum value of the Go type")
	}
	if e := newEnum(c.goType, 0); e.String() != "EntryNormal" {
		panic("convert: EnumInfo.New")
	}
	dst := map[string]any{}
	dv := reflect.ValueOf(dst)
	key := reflect.ValueOf(NamedKey("k"))
	if key.Type().AssignableTo(dv.Type().Key()) || !key.Type().ConvertibleTo(dv.Type().Key()) {
		panic("convert: a named key is convertible, not assignable")
	}
	dv.SetMapIndex(key.Convert(dv.Type().Key()), reflect.ValueOf(1))
	if dst["k"] != 1 {
		panic("convert: SetMapIndex of the converted key")
	}
	if reflect.TypeOf("").ConvertibleTo(c.goType) {
		panic("convert: a string is not convertible to an enum")
	}
}

// REQ reflect/convert (panics): PBValueOf of a value of another type panics "invalid type: got
// reflect.Number, want reflect.EntryType" (protobuf's converter check).
// Specs: none yet.
func MustPanicConvertMismatch() Number {
	c := &enumConverter{goType: reflect.TypeOf(EntryNormal)}
	return c.PBValueOf(reflect.ValueOf(Number(1)))
}

// REQ reflect/convert (panics): Convert of a string to an enum type panics
// "reflect.Value.Convert: value of type string cannot be converted to type reflect.EntryType".
// Specs: none yet.
func MustPanicConvertString() reflect.Value {
	return reflect.ValueOf("x").Convert(reflect.TypeOf(EntryNormal))
}
