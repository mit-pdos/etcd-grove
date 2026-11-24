package reflect

// encoding/binary's reflective path: Read, Write and Size of a fixed-size
// struct.
//
// Mirrors etcd pkg/v3 netutil/routes_linux.go:113,148,177 (`binary.Read(buf,
// cpuutil.ByteOrder(), &rtmsg)` into syscall.RtMsg, IfAddrmsg, IfInfomsg:
// structs of uint8/uint16/uint32 fields) and Go 1.27.3
// encoding/binary/binary.go: Read (:258-283: the fast path for basic types
// and their slices, else `v := reflect.ValueOf(data)`, Pointer -> Elem, Slice
// as is, anything else the error "binary.Read: invalid type"), Write and Size
// (:410-426, :689: `dataSize(reflect.Indirect(reflect.ValueOf(v)))`, cached
// per struct type in a sync.Map; sizeof (:733-760) recurses over Array and
// Struct and is -1 for int, string, slices of structs, ...: Write then fails
// "binary.Write: some values are not fixed-sized in type T"), and the walks
// decoder.value/encoder.value (:845-985: Index, NumField, Field(i); a field
// named "_" is skipped on decode and written as zeros on encode). etcd's
// other binary calls (wal decoder.go:232, rafthttp msgappv2_codec.go,
// msg_codec.go) pass a scalar or *scalar and take the fast path.
//
// Go's panic: Read into a struct with an unexported field not named "_"
// panics in reflect "reflect: reflect.Value.SetUint using value obtained
// using unexported field".
//
// To prove: Size is the sum of the fields' sizes (12 for RtMsg) and -1 for a
// struct with an int field; Write of a fixed-size struct writes its fields in
// order in the byte order given, zeros for "_"; Read of the bytes gives the
// struct back (but "_"); neither panics on exported or "_" fields.
//
// Needs R1 (Kind, Size of basic types, NumField, Field(i).Name, Elem, Len)
// and R2 (ValueOf, Indirect, Elem, Field, Index, SetUint/SetInt/SetBool,
// Uint/Int, CanSet).

import (
	"bytes"
	"encoding/binary"
)

// RtMsg is syscall.RtMsg (linux/amd64).
type RtMsg struct {
	Family   uint8
	Dst_len  uint8
	Src_len  uint8
	Tos      uint8
	Table    uint8
	Protocol uint8
	Scope    uint8
	Type     uint8
	Flags    uint32
}

type padded struct {
	A uint16
	_ uint16
	B uint32
}

type notFixed struct {
	A uint8
	N int
}

type withUnexportedField struct {
	A uint8
	b uint8
}

// REQ reflect/binary-rw: binary.Size of RtMsg is 12 and of a struct with an int field -1;
// Write then Read of an RtMsg gives it back; a "_" field is written as zeros and skipped on
// read; Write of a non-fixed-size struct and Read into a non-pointer struct are errors, not
// panics.
// Users: etcd pkg/v3 netutil/routes_linux.go:113,148,177.
// Assumes: nothing.
// Specs: none yet; needs R1 and R2 (doc.go).
func ReqBinaryRW() {
	if binary.Size(RtMsg{}) != 12 || binary.Size(&RtMsg{}) != 12 || binary.Size(notFixed{}) != -1 {
		panic("binary-rw: Size")
	}
	in := RtMsg{Family: 2, Dst_len: 0, Table: 254, Flags: 0x01020304}
	var buf bytes.Buffer
	if err := binary.Write(&buf, binary.LittleEndian, &in); err != nil || buf.Len() != 12 {
		panic("binary-rw: Write")
	}
	if b := buf.Bytes(); b[0] != 2 || b[4] != 254 || b[8] != 4 || b[11] != 1 {
		panic("binary-rw: field order and byte order")
	}
	var out RtMsg
	if err := binary.Read(bytes.NewReader(buf.Bytes()), binary.LittleEndian, &out); err != nil || out != in {
		panic("binary-rw: Read gives the struct back")
	}
	var pb bytes.Buffer
	if err := binary.Write(&pb, binary.BigEndian, padded{A: 1, B: 2}); err != nil ||
		!bytes.Equal(pb.Bytes(), []byte{0, 1, 0, 0, 0, 0, 0, 2}) {
		panic("binary-rw: a _ field is zeros")
	}
	var p padded
	if err := binary.Read(bytes.NewReader([]byte{0, 1, 9, 9, 0, 0, 0, 2}), binary.BigEndian, &p); err != nil || p.A != 1 || p.B != 2 {
		panic("binary-rw: a _ field is skipped")
	}
	if err := binary.Write(&pb, binary.LittleEndian, notFixed{}); err == nil {
		panic("binary-rw: Write of a non-fixed-size struct")
	}
	if err := binary.Read(bytes.NewReader(buf.Bytes()), binary.LittleEndian, out); err == nil {
		panic("binary-rw: Read into a non-pointer")
	}
}

// REQ reflect/binary-rw (panics): Read into a struct with an unexported field (not "_") panics
// "reflect: reflect.Value.SetUint using value obtained using unexported field".
// Specs: none yet.
func MustPanicBinaryReadUnexported() {
	var w withUnexportedField
	_ = binary.Read(bytes.NewReader([]byte{1, 2}), binary.LittleEndian, &w)
}
