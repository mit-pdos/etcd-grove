// Package protoreflect is the dsverify lab's stand-in for
// google.golang.org/protobuf/reflect/protoreflect (v1.36.12) in a kit's model build
// (notes/grpc-model.md): only the names that protoc-gen-go's generated code (*.pb.go) refers to,
// so that it compiles unmodified against the protobuf model. Reflection is not modeled: the
// descriptor and message interfaces are empty, so code that uses reflection does not compile in
// the model build (outside the subset), and the generated methods that return them
// (ProtoReflect, Descriptor, ...) are names only for Goose (kitgen's [protobuf]).
package protoreflect

// ProtoMessage is the interface every generated message implements (as the real package's).
type ProtoMessage interface {
	ProtoReflect() Message
}

// Message is a reflective view of a message; not modeled.
type Message interface{}

// FileDescriptor describes a .proto file; not modeled.
type FileDescriptor interface{}

// EnumDescriptor describes an enum; not modeled.
type EnumDescriptor interface{}

// EnumType is an enum's type; not modeled.
type EnumType interface{}

// EnumNumber is the numeric value of an enum (as the real package's).
type EnumNumber int32
