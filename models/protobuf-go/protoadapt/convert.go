// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package protoadapt bridges the original and new proto APIs.
package protoadapt

import (
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/runtime/protoiface"
	"google.golang.org/protobuf/runtime/protoimpl"
)

// MessageV1 is the original [github.com/golang/protobuf/proto.Message] type.
type MessageV1 = protoiface.MessageV1

// MessageV2 is the [google.golang.org/protobuf/proto.Message] type used by the
// current [google.golang.org/protobuf] module, adding support for reflection.
type MessageV2 = proto.Message

// MessageV1Of converts a v2 message to a v1 message.
// It returns nil if m is nil.
func MessageV1Of(m MessageV2) MessageV1 {
	return protoimpl.X.ProtoMessageV1Of(m)
}

// MessageV2Of converts a v1 message to a v2 message.
// It returns nil if m is nil.
func MessageV2Of(m MessageV1) MessageV2 {
	// MODEL: a message that is already a v2 message is returned as it is (protoimpl's
	// ProtoMessageV2Of, internal/impl/api_export.go:127-135, through protoMessageV2Of, 110-123: a
	// nil interface gives nil, a protoreflect.ProtoMessage itself); a v1-only message (wrapped by
	// protobuf-go's legacy path, which the model does not have) is not modelled.
	if m == nil {
		return nil
	}
	if v2, ok := m.(MessageV2); ok {
		return v2
	}
	panic(proto.NotModelled("protobuf model: protoadapt.MessageV2Of of a message that is not a v2 message"))
}
