package unsafereflect

// Example 3: protoreflect.Value, a union packed by hand.
//
// Mirrors google.golang.org/protobuf@v1.36.12/reflect/protoreflect/
// value_unsafe.go (all of it) and value_union.go (the accessors and their
// panics), and internal/strs/strings_unsafe.go:19,27 (UnsafeString,
// UnsafeBytes).
//
// A Value is three words: a type word, a data pointer and a number. A string
// is stored as (stringType, StringData(s), len(s)) and read back with
// unsafe.String. A message is stored as the two words of its interface value,
// read off the interface's memory through an ifaceHeader cast, and rebuilt by
// writing an ifaceHeader into an `any`. The type words are taken from
// interface values of constants (typeOf(""), typeOf([]byte(nil))), so they
// are the run-time type descriptors' addresses. Every list, map and message
// field access through protoreflect (protojson, prototext, proto.Equal,
// proto.Merge and Clone, which etcd's server and raft call) returns a Value.
//
// To prove: each accessor matches its constructor, so the panics
// ("type mismatch: cannot convert ...") are unreachable; the rebuilt
// interface is the original one; and UnsafeString's result is used only while
// the bytes under it are not written (the map lookup below), since a string
// is immutable.
//
// Needs U3: the representation of strings, slices and interfaces (empty ones:
// type descriptor and data; non-empty ones: itab and data, so a model must
// tell them apart), with unsafe.String/StringData/SliceData/Slice over it;
// interface type words as comparable values; and ownership for the aliasing (unsafe.String gives up
// the right to write the bytes while the string lives).

import "unsafe"

type ifaceHeader struct {
	_    [0]any // if interfaces have greater alignment than unsafe.Pointer, this will enforce it.
	Type unsafe.Pointer
	Data unsafe.Pointer
}

var (
	nilType     = typeOf(nil)
	stringType  = typeOf("")
	bytesType2  = typeOf([]byte(nil))
	uint64Type2 = typeOf(uint64(0))
)

// typeOf returns a pointer to the Go type information. The pointer is
// comparable and equal if and only if the types are identical.
func typeOf(t any) unsafe.Pointer {
	return (*ifaceHeader)(unsafe.Pointer(&t)).Type
}

// ProtoMessage stands for protoreflect.ProtoMessage.
type ProtoMessage interface{ ProtoReflect() any }

// Value is protoreflect.Value.
type Value struct {
	_   [0]func() // prevent comparability
	typ unsafe.Pointer
	ptr unsafe.Pointer
	num uint64
}

func ValueOfUint64(v uint64) Value { return Value{typ: uint64Type2, num: v} }

func ValueOfString(v string) Value {
	return Value{typ: stringType, ptr: unsafe.Pointer(unsafe.StringData(v)), num: uint64(len(v))}
}

func ValueOfBytes(v []byte) Value {
	return Value{typ: bytesType2, ptr: unsafe.Pointer(unsafe.SliceData(v)), num: uint64(len(v))}
}

// valueOfIface stores the two words of an empty interface value
// (value_unsafe.go:70).
func valueOfIface(v any) Value {
	p := (*ifaceHeader)(unsafe.Pointer(&v))
	return Value{typ: p.Type, ptr: p.Data}
}

// ValueOfMessage converts to `any` first (value_union.go:176). Reading the
// header of v itself would be wrong: the first word of a non-empty
// interface is an itab, not a type descriptor, and the `any` getIface
// rebuilds from it is not a message (a first draft of this snippet did that,
// and its Message() panicked).
func ValueOfMessage(v ProtoMessage) Value { return valueOfIface(v) }

func (v Value) getIface() (x any) {
	*(*ifaceHeader)(unsafe.Pointer(&x)) = ifaceHeader{Type: v.typ, Data: v.ptr}
	return x
}

func (v Value) Uint() uint64 {
	if v.typ != uint64Type2 {
		panic("type mismatch: cannot convert to uint")
	}
	return v.num
}

func (v Value) String() string {
	if v.typ != stringType {
		panic("type mismatch: cannot convert to string")
	}
	return unsafe.String((*byte)(v.ptr), v.num)
}

func (v Value) Bytes() []byte {
	if v.typ != bytesType2 {
		panic("type mismatch: cannot convert to bytes")
	}
	return unsafe.Slice((*byte)(v.ptr), v.num)
}

func (v Value) Message() ProtoMessage {
	switch vi := v.getIface().(type) {
	case ProtoMessage:
		return vi
	default:
		panic("type mismatch: cannot convert to message")
	}
}

// UnsafeString is strs.UnsafeString: the string aliases b.
func UnsafeString(b []byte) string { return unsafe.String(unsafe.SliceData(b), len(b)) }

// REQ unsafereflect/value-union: a protoreflect.Value read with the accessor of its constructor
// gives the value back (the "type mismatch" panics are unreachable; bytes alias the original), a
// message's Value gives the same message, and a string made by UnsafeString may be used for a map
// lookup over a buffer that is written once the string is dead.
// Users: every protoreflect access (proto.Equal, Merge, Clone, protojson, prototext: etcd's server
// and raft call Clone and Equal); reflect/protoreflect/value_unsafe.go, internal/strs.
// Assumes: nothing.
// Specs: none yet; needs U3 (doc.go), with unsafe.String giving up the right to write the bytes
// while the string lives.
func ReqValueUnion() *Entry {
	e := &Entry{Term: 1}
	data := []byte("val")
	vu, vs, vb, vm := ValueOfUint64(5), ValueOfString("key"), ValueOfBytes(data), ValueOfMessage(e)
	if vu.Uint() != 5 || vs.String() != "key" || &vb.Bytes()[0] != &data[0] {
		panic("value-union: scalar round trip")
	}
	back, ok := vm.Message().(*Entry)
	if !ok || back != e {
		panic("value-union: not the same message")
	}

	byName := map[string]int{"Term": 2, "Data": 4}
	buf := []byte("Term")
	num := byName[UnsafeString(buf)] // the string is dead after the lookup
	copy(buf, "Data")                // so the buffer may be written again
	if num != 2 {
		panic("value-union: lookup")
	}
	return back
}
