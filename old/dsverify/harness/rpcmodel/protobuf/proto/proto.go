// Package proto is the dsverify lab's model of google.golang.org/protobuf/proto (v1.36.12): the
// subset a kit's targets use, Marshal and Unmarshal (notes/grpc-model.md). Goose translates it in
// place of the real package; the harness proves its specs once (harness/lean/Harness/Proof/grpc).
//
// Reflection is replaced by a Codec that the kit's generated code registers (harness/kitgen,
// kit.toml's [protobuf]): encoders and decoders for exactly the kit's listed message types, which
// write and read protobuf's wire format byte for byte as the real package does (tested against it
// by the generated tests). A message of an unlisted type makes the codec panic: outside the
// subset, never a silent difference.
//
// Semantics (the trusted claim): Marshal(m) returns what the real Marshal returns for m: nil and
// no error for a nil interface, else the encoding (fields in field-number order, proto3's default
// values omitted), or an error where the real one errs (a string field that is not UTF-8);
// Unmarshal(b, m) resets *m and decodes b into it, or returns an error where the real one does
// (malformed input, a string field that is not UTF-8, nesting deeper than 10000). Unknown fields
// are skipped, not kept (the real package keeps them and Marshal writes them back: no node of a
// theorem writes any, since every node runs the same codec). Error values are the codec's: only
// error-or-not is modeled, not the messages.
package proto

import (
	"sync"

	"google.golang.org/protobuf/reflect/protoreflect"
)

// Message is the top-level interface that all messages implement (as the real package's).
type Message = protoreflect.ProtoMessage

// Codec is the model's stand-in for protobuf's reflection: a kit's generated encoder and decoder
// for exactly the message types kit.toml's [protobuf] lists (harness/kitgen/pbgen.py). It is not
// in the real package; the kit's generated registerProto (built only for the model, build tags
// rpcmodel or goose) calls SetCodec, and the real build has a no-op in its place.
//
//   - Marshal(m): m is a pointer to a listed message type (possibly nil); its encoding, or an
//     error where the real Marshal errs. Panics for any other value.
//   - Unmarshal(b, m): m is a non-nil pointer to a listed message type; resets *m and decodes b
//     into it, or returns an error where the real Unmarshal errs. Panics for any other value.
type Codec struct {
	Marshal   func(m interface{}) ([]byte, error)
	Unmarshal func(b []byte, m interface{}) error
}

var codecMu sync.Mutex
var codec *Codec

// SetCodec registers the kit's codec; the first registration stays. Not in the real package.
func SetCodec(c *Codec) {
	codecMu.Lock()
	if codec == nil {
		codec = c
	}
	codecMu.Unlock()
}

func getCodec() *Codec {
	codecMu.Lock()
	c := codec
	codecMu.Unlock()
	if c == nil {
		panic("protobuf model: no codec registered (the kit's registerProto)")
	}
	return c
}

// Marshal returns the wire-format encoding of m (as the real package's Marshal).
func Marshal(m Message) ([]byte, error) {
	if m == nil {
		return nil, nil
	}
	return getCodec().Marshal(m)
}

// Unmarshal parses the wire-format message in b and places the result in m (as the real
// package's Unmarshal: m is reset first).
func Unmarshal(b []byte, m Message) error {
	return getCodec().Unmarshal(b, m)
}

// MarshalValue is Marshal for a message in a value of static type interface{} (the grpc model's
// codec calls it, as the real grpc's proto codec calls Marshal; the caller has ruled out a nil
// interface). Not in the real package.
func MarshalValue(v interface{}) ([]byte, error) {
	return getCodec().Marshal(v)
}

// UnmarshalValue is Unmarshal for a value of static type interface{}. Not in the real package.
func UnmarshalValue(b []byte, v interface{}) error {
	return getCodec().Unmarshal(b, v)
}
