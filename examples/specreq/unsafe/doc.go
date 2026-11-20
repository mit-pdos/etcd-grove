// Package unsafe holds requirement snippets for a semantics of Go's `unsafe`
// beyond plain bytes: the uses a proof of all of etcd would have to prove
// panic-free, nearly all in protobuf-go's runtime (internal/impl,
// reflect/protoreflect), which every generated *.pb.go file and grpc's codec
// call. Each file is a minimized but faithful copy of real code at etcd's pins
// (protobuf-go v1.36.12, grpc v1.84.0, Go 1.27.3), with the original's
// location. Each function Req* is a requirement snippet
// (notes/specs-only/README.md, "Requirement snippets"): what its users rely on
// is a panic on its violation, so a semantics of unsafe, and specs over it, are
// adequate only if every snippet is provably panic-free from them. No spec
// exists yet (each says "Specs: none yet" and the capabilities it needs);
// snippets_test.go runs them all. The reflect snippets are in
// examples/specreq/reflect, whose R1-R3 these snippets also cite where
// protobuf takes its offsets and types from reflection.
//
// # What Perennial has today
//
// Byte views of plain (pointer-free) types: R1-R5 of Perennial's
// docs/design/unsafe-memory.md, for bbolt. Layout constants (Sizeof,
// Offsetof, Alignof), byte loads and stores that check cells, unsafe.Add and
// unsafe.Slice as arithmetic, and integer atomics as byte atomics. `*T <->
// unsafe.Pointer` is the identity on locations, and `uintptr <-> pointer` is
// stuck. Every protobuf operation (Marshal, Unmarshal, Size, Clone) is an
// axiom here, stated per message type (Spec/google_golang_org/protobuf/proto/).
//
// # What is missing
//
//	U1 struct layout for every type, including pointer-carrying ones: a field's
//	   address is the struct's address plus StructField.Offset, so `base+off`
//	   reached by uintptr arithmetic is `&s.f` (codec.go).
//	U2 representation-compatible casts between types with the same layout
//	   that carry pointers: *T, unsafe.Pointer, struct{p unsafe.Pointer};
//	   []*T read as []pointer; *Msg read as *FirstField (codec.go,
//	   messagestate.go). Cells hold words with provenance, not bytes: a pointer
//	   cannot be bytes.
//	U3 the representation of strings (data, len), slices (data, len, cap) and
//	   interfaces (empty: type word, data word; non-empty: itab, data word),
//	   with unsafe.String/StringData/SliceData/Slice over it, and the rule that
//	   the bytes under a string are never written again (value.go).
//	U4 pointer atomics on a field reached through a cast:
//	   atomic.LoadPointer((*unsafe.Pointer)(unsafe.Pointer(&ms.f)))
//	   (messagestate.go).
//
// # The snippets
//
//	codec.go         REQ unsafe/offset-codec   table-driven marshal: offsets, typed casts   U1 U2 (R1 R3)
//	messagestate.go  REQ unsafe/message-state  ProtoReflect: *Msg as *messageState, atomics U2 U4 (R3)
//	value.go         REQ unsafe/value-union    protoreflect.Value: headers, unsafe.String   U3
//
// # Why panic-freedom is provable at all
//
// The unsafe accesses rest on one invariant per message type, established when
// its coder is built from reflection over the Go struct: every coder field's
// offset and kind agree with a field of the struct (codec.go; the facts it is
// built from are reflect's struct-tags snippet). What cannot be configured
// away: protobuf-go v1.36.12 has no reflect-only build any more (the `purego`
// pointer_reflect.go is gone), so a protobuf without unsafe would be a fork.
package unsafe
