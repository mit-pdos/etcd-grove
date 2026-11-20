// Package protoimpl is the dsverify lab's stand-in for
// google.golang.org/protobuf/runtime/protoimpl (v1.36.12) in a kit's model build
// (notes/grpc-model.md): only the names that protoc-gen-go's generated code (*.pb.go, generator
// versions 1.2x to 1.36) refers to, so that it compiles unmodified against the protobuf model.
// Nothing here is reflection: the message state is empty, the type builder builds nothing, and
// the generated functions that use them (Reset's state, ProtoReflect, String, Descriptor, the
// file's descriptor initialization) are names only for Goose (kitgen's [protobuf]), with the
// file's initialization trusted to do nothing a program can observe without reflection.
package protoimpl

import "google.golang.org/protobuf/reflect/protoreflect"

// The generated code's version checks (EnforceVersion(GenVersion - MinVersion) and
// EnforceVersion(MaxVersion - GenVersion) must be constants of an unsigned type).
const (
	MaxVersion = 36
	GenVersion = 20
	MinVersion = 0
)

// EnforceVersion is the generated code's version check type.
type EnforceVersion uint

// UnsafeEnabled: the model has no unsafe fast path.
const UnsafeEnabled = false

// Pointer is the generated code's opaque message pointer (the real one is unsafe.Pointer).
type Pointer = interface{}

// MessageState is a message's internal state (empty in the model).
type MessageState struct{}

// LoadMessageInfo returns nil (the model keeps no message info).
func (ms *MessageState) LoadMessageInfo() *MessageInfo {
	return nil
}

// StoreMessageInfo does nothing.
func (ms *MessageState) StoreMessageInfo(mi *MessageInfo) {}

// SizeCache is a message's cached size (as the real alias).
type SizeCache = int32

// UnknownFields is a message's unknown fields (as the real alias; the model's codec skips
// unknown fields and never fills it).
type UnknownFields = []byte

// MessageInfo is a message type's information (unused by the model).
type MessageInfo struct {
	GoReflectType interface{}
	Desc          interface{}
	Exporter      func(v interface{}, i int) interface{}
	OneofWrappers []interface{}
}

// MessageOf returns a reflective view of m (none in the model).
func (mi *MessageInfo) MessageOf(m interface{}) protoreflect.Message {
	return nil
}

// EnumInfo is an enum type's information (unused by the model).
type EnumInfo struct {
	GoReflectType interface{}
	Desc          interface{}
}

// Descriptor returns the enum's descriptor (none in the model).
func (ei *EnumInfo) Descriptor() protoreflect.EnumDescriptor {
	return nil
}

// ExtensionInfo is an extension's information (unused by the model).
type ExtensionInfo struct{}

// DescBuilder is a file descriptor's builder (unused by the model).
type DescBuilder struct {
	GoPackagePath string
	RawDescriptor []byte
	NumEnums      int32
	NumMessages   int32
	NumExtensions int32
	NumServices   int32
}

// TypeBuilder builds a file's types (nothing, in the model).
type TypeBuilder struct {
	File              DescBuilder
	GoTypes           []interface{}
	DependencyIndexes []int32
	EnumInfos         []EnumInfo
	MessageInfos      []MessageInfo
	ExtensionInfos    []ExtensionInfo
}

// Out is what Build returns.
type Out struct {
	File protoreflect.FileDescriptor
}

// Build builds nothing (the model has no descriptors).
func (tb TypeBuilder) Build() Out {
	return Out{}
}

// Export is the type of X, the generated code's helpers.
type Export struct{}

// X is the generated code's helpers.
var X Export

// MessageStateOf returns a message's state (a fresh empty one in the model).
func (Export) MessageStateOf(p Pointer) *MessageState {
	return new(MessageState)
}

// MessageStringOf returns m's text format; the model returns "" (String() on a generated message
// is names only for Goose).
func (Export) MessageStringOf(m protoreflect.ProtoMessage) string {
	return ""
}

// EnumStringOf returns an enum value's name; the model returns "" (names only for Goose).
func (Export) EnumStringOf(ed protoreflect.EnumDescriptor, n protoreflect.EnumNumber) string {
	return ""
}

// CompressGZIP returns its input (the model does not compress; names only for Goose).
func (Export) CompressGZIP(in []byte) []byte {
	return in
}
