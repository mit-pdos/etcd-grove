//go:build !protomodel

package pbmodeltest

import (
	"testing"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

const modelBuild = false

// TestNotModelled, real build: what the model does not model works in protobuf-go (the model
// panics with NotModelled instead: mode_model_test.go).
func TestNotModelled(t *testing.T) {
	for name, f := range notModelledCases() {
		if o := outcome(f); o != "ok" {
			t.Errorf("%s: protobuf-go: %s", name, o)
		}
	}
}

func notModelledCases() map[string]func() {
	return map[string]func(){
		"Marshal of a type without methods": func() { _, _ = proto.Marshal(&descriptorpb.FileDescriptorProto{}) },
		"UnmarshalOptions{DiscardUnknown}": func() {
			_ = proto.UnmarshalOptions{DiscardUnknown: true}.Unmarshal(nil, &descriptorpb.FileDescriptorProto{})
		},
		"Size of a type without methods":  func() { _ = proto.Size(&descriptorpb.FileDescriptorProto{}) },
		"Clone of a type without methods": func() { _ = proto.Clone(&descriptorpb.FileDescriptorProto{}) },
	}
}
