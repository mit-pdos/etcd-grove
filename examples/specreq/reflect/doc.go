// Package reflect holds requirement snippets for a semantics of Go's `reflect`
// (and of the standard library's internal/reflectlite, which errors uses): the
// uses a proof of all of etcd would have to prove panic-free, in protobuf-go's
// runtime, grpc, net/http and errors. Each file is a minimized but faithful
// copy of real code at etcd's pins (protobuf-go v1.36.12, grpc v1.84.0, Go
// 1.27.3), with the original's location. Each function Req* is a requirement
// snippet (notes/specs-only/README.md, "Requirement snippets"): what its users
// rely on is a panic on its violation, so a semantics of reflect, and specs
// over it, are adequate only if every snippet is provably panic-free from
// them. No spec exists yet (each says "Specs: none yet" and the capabilities
// it needs); snippets_test.go runs them all. The unsafe snippets are in
// examples/specreq/unsafe.
//
// # What Perennial has today
//
// reflect is names-only. This repository has 23 trust-boundary axioms for it
// (Spec/reflect/, Proof/reflect/Values.lean), and Goose keeps no struct tags.
//
// # What is missing
//
//	R1 type descriptors as values: identity (==, map keys, including another
//	   package's unexported types), Kind, Elem, String, NumField, Field(i) with
//	   Name, Tag, Offset, Type, Anonymous; NumMethod, Implements, AssignableTo.
//	   Goose must emit them for every type a program declares, struct tags
//	   included.
//	R2 reflect.Value: ValueOf, Zero, New, NewAt, Elem, Field, Interface (with
//	   its panic on values read through unexported fields), Pointer, Set,
//	   IsNil, Len, Index, and the map and slice operations (MapIndex,
//	   SetMapIndex, MapRange, MakeSlice, Append: protobuf's map and list
//	   fields).
//	R3 the bridge to unsafe: an offset from reflect.StructField used with
//	   uintptr arithmetic, v.Pointer(), reflect.NewAt(t, p) (the unsafe
//	   package's codec.go and messagestate.go).
//
// Not semantics, only naming: `//go:linkname` (net/http's clone.go, request.go,
// server.go; net/url; net/textproto) binds a name to a function of another
// package. Goose must resolve it. It needs no rule of the model.
//
// # The snippets
//
//	structtags.go       REQ reflect/struct-tags       message info from tags against the descriptor  R1 R2
//	registerservice.go  REQ reflect/register-service  grpc's RegisterService: Implements, assertions  R1
//	httpunwrap.go       REQ reflect/http-unwrap       net/http: cross-package type identity, Field(0) R1 R2
//	errorsas.go         REQ reflect/errors-as         errors.As (grpc's status.FromError)            R1 R2
//
// # Why panic-freedom is provable at all
//
// Every reflective decision in this code is about a type the program declares
// (a generated message, a service's interface, io.NopCloser's dynamic type),
// and the run-time data the reflection reads is constants (struct tags, the
// raw descriptor bytes in each *.pb.go). So the panics are excluded by facts
// fixed when the program is compiled: "the tags of Entry agree with its
// descriptor" (structtags.go), "the handler type implements the service
// interface" (registerservice.go). A proof needs (a) the semantics above and
// (b) a way to discharge such facts by computation on the translation (a
// generated lemma per message type, or a decision procedure over the type
// descriptors), not by hand in every proof. grpc and net/http use reflect
// directly in only a few places, but they reach errors.As, fmt's %v,
// sort.Slice (reflectlite.Swapper) and reflect.DeepEqual (grpc's service
// config), which Perennial models by hand today.
package reflect
