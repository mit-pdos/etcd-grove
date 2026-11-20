// Command pbgo generates ../../pb/arith.pb.go with protoc-gen-go's generator (v1.36.12) from the
// descriptor below (the difftest's service and messages): the lab has no protoc.
package main

import (
	"os"

	gengo "google.golang.org/protobuf/cmd/protoc-gen-go/internal_gengo"
	"google.golang.org/protobuf/compiler/protogen"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
	"google.golang.org/protobuf/types/pluginpb"
)

func f(name string, num int32, typ descriptorpb.FieldDescriptorProto_Type, rep bool, tn string) *descriptorpb.FieldDescriptorProto {
	l := descriptorpb.FieldDescriptorProto_LABEL_OPTIONAL
	if rep {
		l = descriptorpb.FieldDescriptorProto_LABEL_REPEATED
	}
	fd := &descriptorpb.FieldDescriptorProto{Name: proto.String(name), Number: proto.Int32(num), Type: typ.Enum(), Label: l.Enum(), JsonName: proto.String(name)}
	if tn != "" {
		fd.TypeName = proto.String(tn)
	}
	return fd
}

func main() {
	T := descriptorpb.FieldDescriptorProto_TYPE_INT64
	file := &descriptorpb.FileDescriptorProto{
		Name:    proto.String("arith.proto"),
		Package: proto.String("arith"),
		Syntax:  proto.String("proto3"),
		Options: &descriptorpb.FileOptions{GoPackage: proto.String("dsverify.lab/grpcdifftest/pb")},
		EnumType: []*descriptorpb.EnumDescriptorProto{{
			Name: proto.String("Op"),
			Value: []*descriptorpb.EnumValueDescriptorProto{
				{Name: proto.String("ADD"), Number: proto.Int32(0)},
				{Name: proto.String("SUB"), Number: proto.Int32(1)},
			},
		}},
		MessageType: []*descriptorpb.DescriptorProto{
			{Name: proto.String("Args"), Field: []*descriptorpb.FieldDescriptorProto{
				f("a", 1, T, false, ""), f("b", 2, T, false, ""),
				f("id", 3, descriptorpb.FieldDescriptorProto_TYPE_UINT64, false, ""),
				f("op", 4, descriptorpb.FieldDescriptorProto_TYPE_ENUM, false, ".arith.Op"),
				f("tag", 5, descriptorpb.FieldDescriptorProto_TYPE_STRING, false, ""),
				f("blob", 6, descriptorpb.FieldDescriptorProto_TYPE_BYTES, false, ""),
				f("flag", 7, descriptorpb.FieldDescriptorProto_TYPE_BOOL, false, ""),
				f("xs", 8, T, true, ""),
				f("names", 9, descriptorpb.FieldDescriptorProto_TYPE_STRING, true, ""),
				f("inner", 10, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, false, ".arith.Inner"),
				f("inners", 11, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, true, ".arith.Inner"),
				f("small", 12, descriptorpb.FieldDescriptorProto_TYPE_INT32, false, ""),
				f("usmall", 13, descriptorpb.FieldDescriptorProto_TYPE_UINT32, false, ""),
				f("big", 536870911, T, false, ""),
			}},
			{Name: proto.String("Inner"), Field: []*descriptorpb.FieldDescriptorProto{
				f("k", 1, descriptorpb.FieldDescriptorProto_TYPE_STRING, false, ""),
				f("v", 2, T, false, ""),
				f("sub", 3, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, false, ".arith.Inner"),
			}},
			{Name: proto.String("Reply"), Field: []*descriptorpb.FieldDescriptorProto{
				f("c", 1, T, false, ""),
				f("echo", 2, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, false, ".arith.Args"),
			}},
			{Name: proto.String("Empty")},
		},
		Service: []*descriptorpb.ServiceDescriptorProto{{
			Name: proto.String("Arith"),
			Method: []*descriptorpb.MethodDescriptorProto{
				{Name: proto.String("Add"), InputType: proto.String(".arith.Args"), OutputType: proto.String(".arith.Reply")},
				{Name: proto.String("Div"), InputType: proto.String(".arith.Args"), OutputType: proto.String(".arith.Reply")},
			},
		}},
	}
	req := &pluginpb.CodeGeneratorRequest{FileToGenerate: []string{"arith.proto"}, ProtoFile: []*descriptorpb.FileDescriptorProto{file},
		Parameter: proto.String("paths=source_relative")}
	gen, err := protogen.Options{}.New(req)
	if err != nil {
		panic(err)
	}
	for _, fl := range gen.Files {
		if fl.Generate {
			gengo.GenerateFile(gen, fl)
		}
	}
	resp := gen.Response()
	if resp.Error != nil {
		panic(*resp.Error)
	}
	for _, rf := range resp.File {
		os.WriteFile(rf.GetName(), []byte(rf.GetContent()), 0o644)
	}
}
