package unsafereflect

// Example 4: building a message's info from its struct tags, against its
// descriptor.
//
// Mirrors google.golang.org/protobuf@v1.36.12/internal/impl/message.go:
// 144-200 (makeStructInfo walks reflect.Type.NumField/Field(i), reading each
// field's `protobuf:"..."` tag and its Offset), message_reflect_field.go:
// 30-70 and codec_message.go:100-120 (for each field of the descriptor, the
// Go struct field it names, with panics "missing Go struct field for X" and
// "field X has invalid type: got T, want ...") and getMessageInfo
// (message.go:54: reflect.Zero(mt).Interface().(protoreflect.ProtoMessage)).
// The descriptor is decoded at package init from each *.pb.go's raw
// descriptor constant (file_raft_proto_rawDesc) by internal/filedesc; here it
// is a small text constant.
//
// To prove: the panics are unreachable for every generated message. That is a
// fact about constants: the tags of the struct and the raw descriptor, both
// fixed by protoc-gen-go. A proof should get it by computation on the
// translation (a lemma generated per message type), not by hand.
//
// Needs R1 (type descriptors with struct tags, field names, Offset, Kind;
// Goose must emit tags, which it drops today) and R2 (reflect.Zero,
// Interface, an interface type assertion on the result).

import (
	"reflect"
	"strconv"
	"strings"
	"unsafe"
)

type fieldDesc struct {
	num  uint64
	name string
	kind string // "varint" or "bytes"
}

// parseDesc decodes a descriptor "num:name:kind;...".
func parseDesc(raw string) []fieldDesc {
	var fds []fieldDesc
	for _, f := range strings.Split(raw, ";") {
		parts := strings.Split(f, ":")
		if len(parts) != 3 {
			panic("invalid raw descriptor")
		}
		num, err := strconv.ParseUint(parts[0], 10, 32)
		if err != nil {
			panic("invalid raw descriptor: " + err.Error())
		}
		fds = append(fds, fieldDesc{num: num, name: parts[1], kind: parts[2]})
	}
	return fds
}

// fieldNumber parses a `protobuf:"varint,2,opt,name=Term"` tag
// (internal/encoding/tag.Unmarshal).
func fieldNumber(sf reflect.StructField) (uint64, bool) {
	tag := sf.Tag.Get("protobuf")
	if tag == "" {
		return 0, false
	}
	parts := strings.Split(tag, ",")
	if len(parts) < 2 {
		return 0, false
	}
	n, err := strconv.ParseUint(parts[1], 10, 32)
	return n, err == nil
}

type structInfo struct {
	fieldsByNumber map[uint64]reflect.StructField
}

func makeStructInfo(t reflect.Type) structInfo {
	si := structInfo{fieldsByNumber: map[uint64]reflect.StructField{}}
	for i := 0; i < t.NumField(); i++ {
		f := t.Field(i)
		if n, ok := fieldNumber(f); ok {
			si.fieldsByNumber[n] = f
		}
	}
	return si
}

type fieldInfo struct {
	num    uint64
	offset offset
}

// makeKnownFields matches the descriptor to the struct.
func makeKnownFields(t reflect.Type, fds []fieldDesc) []fieldInfo {
	si := makeStructInfo(t.Elem())
	var fis []fieldInfo
	for _, fd := range fds {
		sf, ok := si.fieldsByNumber[fd.num]
		if !ok || sf.Name != fd.name {
			panic("missing Go struct field for " + fd.name)
		}
		switch fd.kind {
		case "varint":
			if sf.Type.Kind() != reflect.Uint64 {
				panic("field " + fd.name + " has invalid type: got " + sf.Type.String() + ", want uint64")
			}
		case "bytes":
			if k := sf.Type.Kind(); k != reflect.Slice && k != reflect.String {
				panic("field " + fd.name + " has invalid type: got " + sf.Type.String() + ", want slice kind")
			}
		default:
			panic("unknown kind " + fd.kind)
		}
		fis = append(fis, fieldInfo{num: fd.num, offset: offset(sf.Offset)})
	}
	return fis
}

// file_node_proto_rawDesc stands for a *.pb.go's raw descriptor.
const file_node_proto_rawDesc = "2:Term:varint;4:Data:bytes;5:Children:bytes"

// getMessageInfo is message.go:54: a zero value of the type, asserted to
// the message interface.
func getMessageInfo(mt reflect.Type) bool {
	_, ok := reflect.Zero(mt).Interface().(ProtoMessage)
	return ok
}

// REQ unsafereflect/struct-tags: building a generated message's info from its struct tags and its
// raw descriptor does not panic ("missing Go struct field", "invalid type"), each field info's
// offset is its struct field's, and a zero message of the type is a ProtoMessage.
// Users: every generated message's first ProtoReflect (internal/impl/message.go:54-200,
// message_reflect_field.go:30-70, codec_message.go:100-120); the descriptor from each *.pb.go's
// rawDesc, decoded at init by internal/filedesc.
// Assumes: nothing (a fact of constants fixed by protoc-gen-go: the proof should compute it).
// Specs: none yet; needs R1 with struct tags, R2 (doc.go).
func ReqStructTags() []fieldInfo {
	fis := makeKnownFields(reflect.TypeOf((*Node)(nil)), parseDesc(file_node_proto_rawDesc))
	if len(fis) != 3 || fis[0].num != 2 || fis[0].offset != offset(unsafe.Offsetof(Node{}.Term)) {
		panic("struct-tags: wrong field info")
	}
	makeKnownFields(reflect.TypeOf((*Entry)(nil)), parseDesc("2:Term:varint"))
	if !getMessageInfo(reflect.TypeOf((*Entry)(nil))) {
		panic("struct-tags: not a message")
	}
	return fis
}
