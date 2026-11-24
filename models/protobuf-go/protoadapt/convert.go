// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package protoadapt bridges the original and new proto APIs.
package protoadapt

import (
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/runtime/protoiface"
)

// MessageV1 is the original [github.com/golang/protobuf/proto.Message] type.
type MessageV1 = protoiface.MessageV1

// MessageV2 is the [google.golang.org/protobuf/proto.Message] type used by the
// current [google.golang.org/protobuf] module, adding support for reflection.
type MessageV2 = proto.Message

// MessageV1Of converts a v2 message to a v1 message.
// It returns nil if m is nil.
func MessageV1Of(m MessageV2) MessageV1 {
	// MODEL: protoimpl's ProtoMessageV1Of (internal/impl/api_export.go:95-108) on a message that is
	// already a v1 message (protoc-gen-go's have Reset, String and ProtoMessage): the message as it
	// is, nil for a nil interface; any other (a message protobuf-go wraps, legacyMessageWrapper) is
	// not modelled.
	if m == nil {
		return nil
	}
	if v1, ok := m.(MessageV1); ok {
		return v1
	}
	// MODEL: not modelled (stuck): protoadapt.MessageV1Of of a message that is not a v1 message
	stuck()
	return nil // (not reached: stuck does not return)
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
	// MODEL: not modelled (stuck): protoadapt.MessageV2Of of a message that is not a v2 message
	stuck()
	return nil // (not reached: stuck does not return)
}

// stuck is the model's not-modelled point (MODEL: not in protobuf-go's protoadapt; models/README.md, "Not modelled:
// stuck"): where the model does not model protobuf-go's protoadapt's behavior it calls stuck (after a comment
// `MODEL: not modelled (stuck): ...`), which has no behavior. Its Lean model is Perennial's
// internal/gomodel.Stuck, `Panic "not modelled"`: a stuck panic, which no recover catches and no
// WP rule steps, so a proof of the program shows that it never gets here. Not a value panic, which
// a program could recover and so observe a behavior protobuf-go's protoadapt does not have; not a bare `select {}`,
// whose WP has the precondition True and so would prove anything after it. Its Go body blocks
// forever, which the tests detect (models/internal/stuck).
func stuck() {
	select {}
}
