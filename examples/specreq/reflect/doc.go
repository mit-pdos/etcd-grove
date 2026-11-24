// Package reflect holds requirement snippets for a semantics of Go's `reflect`
// (and of the standard library's internal/reflectlite, which errors, sort and
// context use): every way the code we verify uses reflection, in etcd, raft,
// bbolt, Kubernetes' apiserver storage, client-go and apimachinery, and the
// libraries they reach (fmt, encoding/json, encoding/binary, errors, sort,
// context, net/http, net/rpc, grpc, protobuf-go, zap, go-cmp, otel). Each file
// is a minimized but faithful copy of real code at the pins (etcd
// upamanyus/etcd@edc800c6f, bbolt upamanyus/bbolt@ca88bb6a8, k8s apimachinery
// 0b7d352f711c, apiserver 9c4ec15b8038, client-go 569675c57fa3, kubernetes
// 878cfa6c4cc7, protobuf-go v1.36.12, grpc v1.84.0, zap v1.28.0, go-cmp v0.7.0,
// otel v1.47.0, Go 1.27.3), with the original's location; where the real code
// is the standard library's own entry point (errors.Is, sort.Slice,
// binary.Read, fmt.Sprintf, reflect.DeepEqual), the snippet calls it. Each
// function Req* is a requirement snippet (notes/specs-only/README.md,
// "Requirement snippets"): what its users rely on is a panic on its
// violation, so a semantics of reflect, and specs over it, are adequate only
// if every Req* is provably panic-free from them. Each MustPanic* is where Go
// itself panics (its message in snippets_test.go's TestPanics): the semantics
// must not let it return. No spec exists yet (each says "Specs: none yet" and
// the capabilities it needs); snippets_test.go runs them all, and TestMirrors
// checks the minimized copies of encoding/json and net/rpc against the real
// ones. The unsafe snippets are in examples/specreq/unsafe; the ones here
// marked UNSAFE-DEPENDENT (unsafedep.go) need R3 and stay stuck in a
// semantics without unsafe.
//
// The survey behind them (2026-11-24) found these direct reflect calls in
// functions translated with their bodies: the k8s apiserver store
// (storage/etcd3: TypeOf, New, MakeSlice, Append, Copy, Value's Set, Len,
// Cap, IsNil, Elem, Addr, Interface), apimachinery's SetZeroValue (Zero),
// client-go's informer factory and reflector (TypeOf as a map key, String,
// Kind, PkgPath, Name), DeepEqual in the daemon controller, the mutation
// detector, bbolt's freelist and the k8s checker, and etcd's txn.isNil
// (ValueOf(msg).IsNil()). The 19 reflect axioms of etc/tcb-baseline.txt are
// these. Everything else reaches reflection inside a names-only or
// hand-modelled library (fmt, encoding/json, errors, sort, protobuf-go, zap).
//
// # What Perennial has today
//
// reflect is names-only. This repository has 23 trust-boundary axioms for it
// (Spec/reflect/, Proof/reflect/Values.lean), and Goose keeps no struct tags.
//
// # What is missing
//
//	R1 type descriptors as values: identity (==, map keys, including another
//	   package's unexported types), Kind, Elem, Key, String, Name, PkgPath,
//	   Comparable, NumField, Field(i)/FieldByName with Name, Tag, Offset,
//	   Type, Anonymous, IsExported; method sets in order (NumMethod,
//	   Method(i), MethodByName) and func types (NumIn, In, NumOut, Out);
//	   Implements, AssignableTo, ConvertibleTo; constructed types (PointerTo,
//	   SliceOf, ArrayOf, TypeFor) identical to the static ones. Goose must
//	   emit them for every type a program declares, struct tags included.
//	R2 reflect.Value: ValueOf, Indirect, Zero, New, Elem, Addr, Field,
//	   FieldByIndex, FieldByName, Interface (with its panic on values read
//	   through unexported fields: the read-only flag, CanInterface, CanSet),
//	   Set and the typed setters (addressability and assignability checks),
//	   the typed getters, IsNil (its panics on the zero Value and on
//	   non-nillable kinds), IsValid, Len, Cap, Index, Slice, Convert, Call
//	   (a method's Func with the receiver first), and the map and slice
//	   operations (MapIndex, MapKeys, SetMapIndex with deletion, MapRange,
//	   MakeMap, MakeSlice, Append, Copy); DeepEqual and reflectlite's Swapper,
//	   which a semantics may take as primitives.
//	R3 the bridge to unsafe: an offset from reflect.StructField used with
//	   uintptr arithmetic, v.Pointer(), UnsafePointer, UnsafeAddr,
//	   reflect.NewAt(t, p) (the unsafe package's codec.go and
//	   messagestate.go; unsafedep.go). A semantics without unsafe leaves
//	   these stuck.
//
// Not semantics, only naming: `//go:linkname` (net/http's clone.go, request.go,
// server.go; net/url; net/textproto) binds a name to a function of another
// package. Goose must resolve it. It needs no rule of the model.
//
// # The snippets
//
//	file                REQ                              pattern                                        needs
//	structtags.go       reflect/struct-tags              protobuf: message info from tags, Offset       R1 R2
//	registerservice.go  reflect/register-service         grpc RegisterService: Implements               R1
//	httpunwrap.go       reflect/http-unwrap              net/http: cross-package identity, Field(0)     R1 R2
//	errorsas.go         reflect/errors-as                errors.As: AssignableTo, Elem().Set            R1 R2
//	typeident.go        reflect/type-identity            Type ==, map[reflect.Type], String/Name/PkgPath R1
//	typednil.go         reflect/typed-nil                Kind dispatch, IsNil of a typed nil            R2
//	ptrset.go           reflect/ptr-set                  New/Zero/Set through pointers, Addr().Interface R1 R2
//	listitems.go        reflect/list-items               MakeSlice/Copy/Append/Index at a run-time type R1 R2
//	errorsis.go         reflect/errors-is                Comparable (errors.Is, context.WithValue)      R1
//	deepequal.go        reflect/deep-equal               DeepEqual at the verified shapes, a cycle      R1 R2
//	sortslice.go        reflect/sort-slice               sort.Slice: reflectlite Swapper, Len           R2
//	binaryrw.go         reflect/binary-rw                encoding/binary's struct walk, "_" fields      R1 R2
//	fmtprint.go         reflect/fmt-print                %v/%+v/%#v of composites, sorted map keys      R1 R2
//	unexported.go       reflect/unexported               read-only values: Interface and Set panic      R1 R2
//	jsonwalk.go         reflect/json-walk                json (v2) fields by tag, maps, Marshaler, decode R1 R2
//	rpcregister.go      reflect/rpc-register             net/rpc: method sets, func types, Value.Call   R1 R2
//	typeconstruct.go    reflect/type-construct           ArrayOf/SliceOf/PointerTo/TypeFor (otel sets)  R1 R2
//	convert.go          reflect/convert                  Convert, ConvertibleTo (protobuf enums)        R1 R2
//	pbfields.go         reflect/pb-fields                protobuf list/map fields as reflect.Values     R1 R2
//	cmpwalk.go          reflect/cmp-walk                 go-cmp: MethodByName("Equal")+Call, MapKeys    R1 R2
//	unsafedep.go        reflect/unsafe-pointer-identity  UNSAFE-DEPENDENT: Pointer, %p, nested pointers R3
//	                    reflect/unsafe-newat             UNSAFE-DEPENDENT: NewAt + UnsafeAddr + Offset  R3
//
// # The translation
//
// etc/goose.py's project specreq-reflect translates the package
// (Code/github_com/mit_pdos/etcd_grove/examples/specreq/reflect.lean and its
// GeneratedProof): every snippet translates, unsafedep.go included
// (`unsafe.Pointer` conversions and `unsafe.Add` are Goose instructions).
// reflect is Perennial's names-only translation, so each reflect call is a
// `FuncResolve _root_.Perennial.reflect.F` or a `MethodResolve` of
// `reflect.Value`/`reflect.Type'` by method name, with no body behind it: a
// semantics gives those names their meaning. Three adjustments keep the
// translation buildable against the trees it imports: httpunwrap.go tests a
// `&http.Transport{}` instead of `http.DefaultTransport` (the main tree's
// net/http skips that variable), jsonwalk.go declares encoding/json's
// Marshaler interface itself (in Go 1.27.3 an alias of encoding/json/v2's,
// which no tree translates), rpcregister.go has go/token's IsExported for
// ASCII names (go/token is only in the part Net/), and unsafedep.go leaves
// runtime.FuncForPC to the test (Perennial's runtime does not name it).
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
