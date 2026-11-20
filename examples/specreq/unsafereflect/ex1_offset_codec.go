package unsafereflect

// Example 1: protobuf's table-driven codec.
//
// Mirrors google.golang.org/protobuf@v1.36.12/internal/impl:
//   - pointer_unsafe.go:18-145: `pointer` wraps an unsafe.Pointer; Apply adds a
//     field offset with uintptr arithmetic; Uint64/Bytes/PointerSlice cast the
//     result to a typed pointer, reading a []*Entry as a []pointer.
//   - message.go:144-200 (makeStructInfo) and codec_message.go:30-120
//     (makeCoderMethods): the offsets come from reflect.StructField.Offset,
//     one coder per field, chosen by the field's Go type.
//   - codec_gen.go (sizeUint64/appendUint64, ...), codec_field.go
//     (sizeMessageSliceInfo/appendMessageSliceInfo): the per-kind coders.
//
// Every proto.Marshal/Size of an etcd message (raftpb.Entry,
// etcdserverpb.RangeRequest, ...) runs this code; grpc's codec calls it for
// every RPC (grpc@v1.84.0/encoding/proto/proto.go:43-80).
//
// To prove: marshal never panics and is not stuck. That holds because each
// coderField's (offset, kind) agrees with a field of the struct that p points
// to: the cast at p.Apply(f.offset) then has the field's own type. The
// agreement is established once, in buildCoder, from reflect; a proof keeps it
// as an invariant of the coder (one per message type, built lazily and cached
// under a reflect.Type key).
//
// Needs U1 (base+Offset is the field), U2 (*[]*Entry read as *[]pointer;
// pointer{p} as unsafe.Pointer), R1 (NumField, Field(i).Type/Offset, type
// identity as a map key), R3 (v.Pointer() of a reflect.Value).

import (
	"reflect"
	"sync"
	"unsafe"
)

type pointer struct{ p unsafe.Pointer }

type offset uintptr

func pointerOfValue(v reflect.Value) pointer { return pointer{p: unsafe.Pointer(v.Pointer())} }

func (p pointer) IsNil() bool { return p.p == nil }

// Apply is pointer_unsafe.go:67-72: uintptr arithmetic inside one expression
// (rule 3 of unsafe.Pointer's documentation).
func (p pointer) Apply(f offset) pointer {
	if p.IsNil() {
		panic("invalid nil pointer")
	}
	return pointer{p: unsafe.Pointer(uintptr(p.p) + uintptr(f))}
}

func (p pointer) Uint64() *uint64 { return (*uint64)(p.p) }
func (p pointer) Bytes() *[]byte  { return (*[]byte)(p.p) }

// PointerSlice is pointer_unsafe.go:130-134: "Super-tricky - p should point
// to a []*T where T is a message type. We load it as []pointer."
func (p pointer) PointerSlice() []pointer { return *(*[]pointer)(p.p) }

type fieldKind int

const (
	kindUint64 fieldKind = iota
	kindBytes
	kindMessageSlice
)

type coderField struct {
	num    uint64
	offset offset
	kind   fieldKind
	sub    *coderInfo // kindMessageSlice: the element's coder
}

type coderInfo struct {
	fields []coderField
}

var (
	coderMu    sync.Mutex
	coderCache = map[reflect.Type]*coderInfo{}
)

var (
	uint64Type = reflect.TypeOf(uint64(0))
	bytesType  = reflect.TypeOf([]byte(nil))
)

// coderOf is the lazily built, cached coder of a pointer-to-struct type,
// as getMessageInfo (message.go:54) and MessageInfo.init. The cache entry is
// stored before the fields are filled, so a recursive type (Node.Children is
// []*Node) finds its own coder.
func coderOf(t reflect.Type) *coderInfo {
	coderMu.Lock()
	defer coderMu.Unlock()
	return coderOfLocked(t)
}

func coderOfLocked(t reflect.Type) *coderInfo {
	if ci, ok := coderCache[t]; ok {
		return ci
	}
	if t.Kind() != reflect.Pointer || t.Elem().Kind() != reflect.Struct {
		panic("invalid message type: " + t.String())
	}
	ci := &coderInfo{}
	coderCache[t] = ci
	st := t.Elem()
	for i := 0; i < st.NumField(); i++ {
		sf := st.Field(i)
		num, ok := fieldNumber(sf) // from the struct tag: ex4
		if !ok {
			continue // internal fields: state, sizeCache, unknownFields
		}
		f := coderField{num: num, offset: offset(sf.Offset)}
		switch {
		case sf.Type == uint64Type:
			f.kind = kindUint64
		case sf.Type == bytesType:
			f.kind = kindBytes
		case sf.Type.Kind() == reflect.Slice && sf.Type.Elem().Kind() == reflect.Pointer:
			f.kind = kindMessageSlice
			f.sub = coderOfLocked(sf.Type.Elem())
		default:
			panic("field " + sf.Name + " has invalid type: " + sf.Type.String())
		}
		ci.fields = append(ci.fields, f)
	}
	return ci
}

func appendVarint(b []byte, v uint64) []byte {
	for v >= 0x80 {
		b = append(b, byte(v)|0x80)
		v >>= 7
	}
	return append(b, byte(v))
}

func sizeVarint(v uint64) int {
	n := 1
	for v >= 0x80 {
		v >>= 7
		n++
	}
	return n
}

func (ci *coderInfo) size(p pointer) int {
	if p.IsNil() {
		return 0
	}
	n := 0
	for i := range ci.fields {
		f := &ci.fields[i]
		fp := p.Apply(f.offset)
		switch f.kind {
		case kindUint64:
			if v := *fp.Uint64(); v != 0 {
				n += sizeVarint(f.num<<3|0) + sizeVarint(v)
			}
		case kindBytes:
			if v := *fp.Bytes(); len(v) != 0 {
				n += sizeVarint(f.num<<3|2) + sizeVarint(uint64(len(v))) + len(v)
			}
		case kindMessageSlice:
			for _, e := range fp.PointerSlice() {
				m := f.sub.size(e)
				n += sizeVarint(f.num<<3|2) + sizeVarint(uint64(m)) + m
			}
		}
	}
	return n
}

func (ci *coderInfo) marshal(b []byte, p pointer) []byte {
	if p.IsNil() {
		return b
	}
	for i := range ci.fields {
		f := &ci.fields[i]
		fp := p.Apply(f.offset)
		switch f.kind {
		case kindUint64:
			if v := *fp.Uint64(); v != 0 {
				b = appendVarint(appendVarint(b, f.num<<3|0), v)
			}
		case kindBytes:
			if v := *fp.Bytes(); len(v) != 0 {
				b = appendVarint(appendVarint(b, f.num<<3|2), uint64(len(v)))
				b = append(b, v...)
			}
		case kindMessageSlice:
			for _, e := range fp.PointerSlice() {
				b = appendVarint(appendVarint(b, f.num<<3|2), uint64(f.sub.size(e)))
				b = f.sub.marshal(b, e)
			}
		}
	}
	return b
}

// Node is a generated message (as raftpb.Entry, with a repeated message
// field so that the []*Node -> []pointer cast is exercised).
type Node struct {
	state         MessageState // ex2
	sizeCache     int32
	unknownFields []byte

	Term     uint64  `protobuf:"varint,2,opt,name=Term"`
	Data     []byte  `protobuf:"bytes,4,opt,name=Data"`
	Children []*Node `protobuf:"bytes,5,rep,name=Children"`
}

// Marshal is proto.Marshal for one message.
func Marshal(m any) []byte {
	v := reflect.ValueOf(m)
	ci := coderOf(v.Type())
	p := pointerOfValue(v)
	return ci.marshal(make([]byte, 0, ci.size(p)), p)
}

// REQ unsafereflect/offset-codec: proto.Marshal of a generated message (scalar, bytes and repeated
// message fields, a nil element) does not panic, is not stuck on a cast, and produces exactly
// proto.Size bytes (grpc's codec relies on the size: encoding/proto/proto.go:51-64, UseCachedSize);
// the coder is built once per type.
// Users: every proto.Marshal/Size of etcd's messages (raftpb.Entry in the WAL, etcdserverpb in
// every RPC), through internal/impl's coders (pointer_unsafe.go, codec_message.go, codec_field.go).
// Assumes: no other goroutine writes the message during Marshal.
// Specs: none yet; needs U1, U2, R1, R3 (doc.go) and the coder invariant (each coder field's
// offset and kind agree with the struct's field).
func ReqOffsetCodec() []byte {
	n := &Node{Term: 3, Data: []byte("put k v"), Children: []*Node{{Term: 2}, nil, {Data: []byte("x")}}}
	ci := coderOf(reflect.TypeOf(n))
	p := pointer{p: unsafe.Pointer(n)}
	b := Marshal(n)
	if len(b) != ci.size(p) {
		panic("offset-codec: size mismatch")
	}
	if coderOf(reflect.TypeOf(n)) != ci {
		panic("offset-codec: coder not cached by type")
	}
	return b
}
