package codectoolarge

import (
	"strings"
	"testing"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/encoding"
	"google.golang.org/grpc/encoding/proto"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/structpb"
)

// TestMarshalTooLarge marshals, with grpc's proto codec, a valid message whose
// encoding is just over 2^48 bytes, the largest allocation Go allows on
// linux/amd64: one 16 MiB value held 2^24 times (about 150 MiB of memory).
// Marshal should fail with ResourceExhausted, the code grpc uses for a message
// over its size limits (encode rejects any message over 4 GiB), not panic.
func TestMarshalTooLarge(t *testing.T) {
	v := structpb.NewStringValue(strings.Repeat("a", 1<<24))
	l := &structpb.ListValue{Values: make([]*structpb.Value, 1<<24)}
	for i := range l.Values {
		l.Values[i] = v
	}
	_, err := encoding.GetCodecV2(proto.Name).Marshal(l)
	if status.Code(err) != codes.ResourceExhausted {
		t.Fatalf("Marshal: err = %v, want ResourceExhausted", err)
	}
}
