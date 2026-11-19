// Command pbgo generates ../x.pb.go with protoc-gen-go's generator (v1.36.12) from the
// descriptor below: package xpb, messages whose fields have every kind the protobuf codec
// generator (harness/kitgen/pbgen.py) supports that the difftest's other messages lack (sint,
// fixed, sfixed, repeated bool, enum and bytes, a negative enum value, two-byte tags, a
// recursion through another message), for the codec's generated tests.
package main

import (
	"os"

	gengo "google.golang.org/protobuf/cmd/protoc-gen-go/internal_gengo"
	"google.golang.org/protobuf/compiler/protogen"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
	"google.golang.org/protobuf/types/pluginpb"
)

type T = descriptorpb.FieldDescriptorProto_Type

func f(name string, num int32, typ T, rep bool, tn string) *descriptorpb.FieldDescriptorProto {
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
	kinds := []struct {
		name string
		typ  T
		tn   string
	}{
		{"i32", descriptorpb.FieldDescriptorProto_TYPE_INT32, ""},
		{"i64", descriptorpb.FieldDescriptorProto_TYPE_INT64, ""},
		{"u32", descriptorpb.FieldDescriptorProto_TYPE_UINT32, ""},
		{"u64", descriptorpb.FieldDescriptorProto_TYPE_UINT64, ""},
		{"s32", descriptorpb.FieldDescriptorProto_TYPE_SINT32, ""},
		{"s64", descriptorpb.FieldDescriptorProto_TYPE_SINT64, ""},
		{"f32", descriptorpb.FieldDescriptorProto_TYPE_FIXED32, ""},
		{"f64", descriptorpb.FieldDescriptorProto_TYPE_FIXED64, ""},
		{"sf32", descriptorpb.FieldDescriptorProto_TYPE_SFIXED32, ""},
		{"sf64", descriptorpb.FieldDescriptorProto_TYPE_SFIXED64, ""},
		{"b", descriptorpb.FieldDescriptorProto_TYPE_BOOL, ""},
		{"s", descriptorpb.FieldDescriptorProto_TYPE_STRING, ""},
		{"by", descriptorpb.FieldDescriptorProto_TYPE_BYTES, ""},
		{"e", descriptorpb.FieldDescriptorProto_TYPE_ENUM, ".xpb.Color"},
		{"m", descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, ".xpb.Other"},
	}
	var fields []*descriptorpb.FieldDescriptorProto
	for i, k := range kinds {
		fields = append(fields, f(k.name, int32(i+1), k.typ, false, k.tn))
		fields = append(fields, f("r"+k.name, int32(i+16), k.typ, true, k.tn))
	}
	file := &descriptorpb.FileDescriptorProto{
		Name:    proto.String("x.proto"),
		Package: proto.String("xpb"),
		Syntax:  proto.String("proto3"),
		Options: &descriptorpb.FileOptions{GoPackage: proto.String("dsverify.lab/grpcdifftest/codec/xpb")},
		EnumType: []*descriptorpb.EnumDescriptorProto{{
			Name: proto.String("Color"),
			Value: []*descriptorpb.EnumValueDescriptorProto{
				{Name: proto.String("RED"), Number: proto.Int32(0)},
				{Name: proto.String("GREEN"), Number: proto.Int32(1)},
				{Name: proto.String("NEG"), Number: proto.Int32(-5)},
			},
		}},
		MessageType: []*descriptorpb.DescriptorProto{
			{Name: proto.String("Kinds"), Field: fields},
			{Name: proto.String("Other"), Field: []*descriptorpb.FieldDescriptorProto{
				f("back", 1, descriptorpb.FieldDescriptorProto_TYPE_MESSAGE, false, ".xpb.Kinds"),
				f("n", 2047, descriptorpb.FieldDescriptorProto_TYPE_SINT32, false, ""),
				f("w", 2048, descriptorpb.FieldDescriptorProto_TYPE_STRING, true, ""),
			}},
		},
	}
	req := &pluginpb.CodeGeneratorRequest{FileToGenerate: []string{"x.proto"}, ProtoFile: []*descriptorpb.FileDescriptorProto{file},
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
		if err := os.WriteFile(rf.GetName(), []byte(rf.GetContent()), 0o644); err != nil {
			panic(err)
		}
	}
}
