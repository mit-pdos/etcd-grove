//go:build protomodel

package pbmodeltest

import (
	"testing"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/runtime/protoiface"
	"google.golang.org/protobuf/types/descriptorpb"

	"models.lab/internal/pbdifftest/pb"
)

const modelBuild = true

// TestNotModelled, model build: outside the model, a NotModelled panic.
func TestNotModelled(t *testing.T) {
	cases := map[string]func(){
		"Marshal of a type without methods": func() { _, _ = proto.Marshal(&descriptorpb.FileDescriptorProto{}) },
		"UnmarshalOptions{DiscardUnknown}":  func() { _ = proto.UnmarshalOptions{DiscardUnknown: true}.Unmarshal(nil, &pb.Args{}) },
		"UnmarshalOptions{Merge}":           func() { _ = proto.UnmarshalOptions{Merge: true}.Unmarshal(nil, &pb.Args{}) },
		"Size of a type without methods":    func() { _ = proto.Size(&descriptorpb.FileDescriptorProto{}) },
		"Clone of a type without methods":   func() { _ = proto.Clone(&descriptorpb.FileDescriptorProto{}) },
		"MarshalState": func() {
			_, _ = proto.MarshalOptions{}.MarshalState(protoiface.MarshalInput{Message: (&pb.Args{}).ProtoReflect()})
		},
		"UnmarshalState": func() {
			_, _ = proto.UnmarshalOptions{}.UnmarshalState(protoiface.UnmarshalInput{Message: (&pb.Args{}).ProtoReflect()})
		},
	}
	for name, f := range cases {
		if o := outcome(f); o != "panic: NotModelled" {
			t.Errorf("%s: the model: %s", name, o)
		}
	}
}
