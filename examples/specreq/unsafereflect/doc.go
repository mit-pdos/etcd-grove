// Package unsafereflect holds requirement snippets for the kinds of `unsafe` and
// `reflect` code a proof of all of etcd would have to prove panic-free:
// protobuf-go's runtime (which every generated *.pb.go file and grpc's codec
// call), grpc and net/http. Each file is a minimized but faithful copy of
// real code at etcd's pins (grpc v1.84.0, protobuf-go v1.36.12, x/net
// v0.59.0, Go 1.27.3), with the original's location, what a proof must show,
// and which of the capabilities below Perennial's model would need. Each
// function Req* is a requirement snippet (notes/specs-only/README.md,
// "Requirement snippets"): what its users rely on is a panic on its violation,
// so a semantics of unsafe and reflect, and specs over it, are adequate only if
// every snippet is provably panic-free from them. They constrain the design:
// a model too weak to prove one is not enough for etcd. No spec exists yet
// (each says "Specs: none yet" and the capabilities it needs);
// snippets_test.go runs them all.
//
// # What Perennial has today
//
// Byte views of plain (pointer-free) types: R1-R5 of Perennial's
// docs/design/unsafe-memory.md, for bbolt. Layout constants (Sizeof,
// Offsetof, Alignof), byte loads and stores that check cells, unsafe.Add and
// unsafe.Slice as arithmetic, and integer atomics as byte atomics. `*T <->
// unsafe.Pointer` is the identity on locations, and `uintptr <-> pointer` is
// stuck. reflect is names-only: this repository has 23 trust-boundary axioms
// for reflect (Spec/reflect/, Proof/reflect/Values.lean), and every protobuf
// operation (Marshal, Unmarshal, Size, Clone) is an axiom stated per message
// type (Spec/google_golang_org/protobuf/proto/).
//
// # What is missing
//
// Memory and unsafe (U):
//
//	U1 struct layout for every type, including pointer-carrying ones: a field's
//	   address is the struct's address plus StructField.Offset, so `base+off`
//	   reached by uintptr arithmetic is `&s.f` (ex1, ex2).
//	U2 representation-compatible casts between types with the same layout
//	   that carry pointers: *T, unsafe.Pointer, struct{p unsafe.Pointer};
//	   []*T read as []pointer; *Msg read as *FirstField (ex1, ex2). Cells hold
//	   words with provenance, not bytes: a pointer cannot be bytes.
//	U3 the representation of strings (data, len), slices (data, len, cap) and
//	   interfaces (type word, data word), with unsafe.String/StringData/
//	   SliceData/Slice over it, and the rule that the bytes under a string
//	   are never written again (ex3).
//	U4 pointer atomics on a field reached through a cast:
//	   atomic.LoadPointer((*unsafe.Pointer)(unsafe.Pointer(&ms.f))) (ex2).
//
// Reflection (R):
//
//	R1 type descriptors as values: identity (==, map keys), Kind, Elem,
//	   String, NumField, Field(i) with Name, Tag, Offset, Type, Anonymous;
//	   NumMethod, Implements. Goose must emit them for every type a program
//	   declares, struct tags included (it keeps none today) (ex4-ex7).
//	R2 reflect.Value: ValueOf, Zero, New, NewAt, Elem, Field, Interface (with
//	   its panic on values read through unexported fields), Pointer, Set,
//	   IsNil, Len, Index, and the map and slice operations (MapIndex,
//	   SetMapIndex, MapRange, MakeSlice, Append: protobuf's map and list
//	   fields) (ex1, ex4, ex6, ex7).
//	R3 the bridge between them: an offset from reflect.StructField used with
//	   uintptr arithmetic (U1), v.Pointer(), reflect.NewAt(t, p) (ex1, ex2).
//
// Not semantics, only naming: `//go:linkname` (net/http's clone.go, request.go,
// server.go; net/url; net/textproto) binds a name to a function of another
// package. Goose must resolve it. It needs no rule of the model.
//
// # The examples
//
//	ex1_offset_codec.go     protobuf's table-driven codec: offsets, typed casts     U1 U2 R1 R3
//	ex2_message_state.go    ProtoReflect: *Msg as *messageState, atomic info ptr    U2 U4 R3
//	ex3_value_union.go      protoreflect.Value: interface headers, unsafe.String     U3
//	ex4_struct_tags.go      MessageInfo from struct tags against the descriptor     R1 R2
//	ex5_register_service.go grpc's RegisterService: Implements, then assertions     R1
//	ex6_http_unwrap.go      net/http: type identity across packages, Field(0)       R1 R2
//	ex7_errors_as.go        errors.As (grpc's status.FromError): target checks      R1 R2
//
// # Why panic-freedom is provable at all
//
// Every reflective decision in this code is about a type the program declares
// (a generated message, a service's interface, io.NopCloser's dynamic type),
// and the run-time data the reflection reads is constants (struct tags, the
// raw descriptor bytes in each *.pb.go). So the panics are excluded by facts
// fixed when the program is compiled: "the tags of Entry agree with its
// descriptor" (ex4), "the handler type implements the service interface"
// (ex5). A proof needs (a) the semantics above and (b) a way to discharge
// such facts by computation on the translation (a generated lemma per
// message type, or a decision procedure over the type descriptors), not by
// hand in every proof. The unsafe parts then rest on one invariant per
// message type, established when its MessageInfo is built: every coder
// field's offset and kind agree with the Go struct's field (ex1, ex4).
//
// What cannot be configured away: protobuf-go v1.36.12 has no reflect-only
// build any more (the `purego` pointer_reflect.go is gone), so a protobuf
// without unsafe would be a fork. grpc and net/http use reflect directly only
// in a few places (ex5, ex6), but they reach protobuf (grpc's
// encoding/proto codec), errors.As (ex7), fmt's %v, sort.Slice
// (reflectlite.Swapper) and sync/atomic.Value, which Perennial models by hand
// today.
package unsafereflect
