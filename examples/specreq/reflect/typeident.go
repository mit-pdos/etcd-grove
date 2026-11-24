package reflect

// Type identity and type names: reflect.Type as a value compared with ==,
// used as a map key, and printed.
//
// Mirrors:
//   - k8s.io/client-go@v0.0.0-20261021054439-569675c57fa3/informers/factory.go:
//     87 and 258 (InformerFor: `informerType := reflect.TypeOf(obj)`, the
//     factory's `informers map[reflect.Type]cache.SharedIndexInformer`, one
//     informer per object type);
//   - client-go tools/cache/reflector.go:1014 (`if e, a := expectedType,
//     reflect.TypeOf(event.Object); e != a {` skips an event of another type)
//     and :339, 378 (TypeOf(expectedType).String() names the reflector);
//   - client-go tools/cache/event_handler_name.go:47-63 (nameForHandler:
//     ValueOf(handler), Kind Interface or Pointer, Elem, then
//     Type().PkgPath() + "." + Type().Name());
//   - k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/pkg/storage/etcd3/
//     store.go:218, 1319 (getTypeName: reflect.TypeOf(obj).String());
//   - every generated *.pb.go's init: `GoPackagePath: reflect.TypeOf(x{}).PkgPath()`
//     (etcd api/v3 etcdserverpb/rpc.pb.go:6950, with `type x struct{}`);
//   - Go 1.27.3 net/http/client.go:343 (TypeOf(rt).String() ==
//     "*http2.Transport"), context/context.go:540 (reflectlite
//     TypeOf(c).String()), fmt/print.go:689 (%T).
// The k8s and client-go functions are translated with their bodies
// (Code/k8s_io/client_go/informers.lean, tools/cache/chunk0.lean,
// Code/k8s_io/apiserver/pkg/storage/etcd3.lean): their proofs step into
// these reflect calls.
//
// To prove: two TypeOf results are equal iff the dynamic types are identical
// (so the factory's map has one entry per type and the reflector's check
// passes exactly the expected type), and String, Name and PkgPath are the
// names Go prints: "*reflect.Pod" for a pointer (Name "" and PkgPath ""), a
// defined type's Name and its package's import path.
//
// Needs R1 (type descriptors as values with ==, hashing as a map key,
// String, Name, PkgPath, Kind, Elem) and R2 (ValueOf, Value.Type, Kind,
// IsNil, Elem).

import (
	"fmt"
	"reflect"
)

// Pod and Node2 stand for two API object types (`runtime.Object`s).
type Pod struct{ Name string }
type Node2 struct{ Name string }

type informer struct{ objType string }

// informerFactory is sharedInformerFactory, minimized: one informer per type.
type informerFactory struct {
	informers map[reflect.Type]*informer
}

// InformerFor is factory.go:254-275.
func (f *informerFactory) InformerFor(obj any) *informer {
	informerType := reflect.TypeOf(obj)
	if inf, ok := f.informers[informerType]; ok {
		return inf
	}
	inf := &informer{objType: getTypeName(obj)}
	f.informers[informerType] = inf
	return inf
}

// getTypeName is etcd3/store.go:1318.
func getTypeName(obj any) string { return reflect.TypeOf(obj).String() }

// acceptEvent is the reflector's type check (reflector.go:1013-1016).
func acceptEvent(expectedType reflect.Type, obj any) bool {
	if expectedType != nil {
		if e, a := expectedType, reflect.TypeOf(obj); e != a {
			return false
		}
	}
	return true
}

// handlerName is nameForHandler's default case (event_handler_name.go:47-63).
func handlerName(handler any) string {
	value := reflect.ValueOf(handler)
	if value.Type().Kind() == reflect.Interface {
		value = value.Elem()
	}
	if value.Type().Kind() == reflect.Pointer {
		if !value.IsNil() {
			value = value.Elem()
		}
	}
	name := value.Type().PkgPath()
	if name != "" {
		name += "."
	}
	if typeName := value.Type().Name(); typeName != "" {
		name += typeName
	}
	return name
}

type x struct{}

const pkgPath = "github.com/mit-pdos/etcd-grove/examples/specreq/reflect"

// REQ reflect/type-identity: reflect.Type values are equal iff the types are identical (one
// informer per type, the reflector's check passes exactly the expected type), work as map keys,
// and print as Go prints them (String "*reflect.Pod", Name, PkgPath, %T).
// Users: client-go informers/factory.go:87,258, tools/cache/reflector.go:339,378,1014,
// event_handler_name.go:47-63; apiserver storage/etcd3/store.go:218,1319; every *.pb.go init
// (TypeOf(x{}).PkgPath()); net/http client.go:343; context.go:540; fmt %T.
// Assumes: nothing.
// Specs: none yet; needs R1 (==, hash, String, Name, PkgPath, Kind, Elem) and R2 (doc.go).
func ReqTypeIdentity() {
	f := &informerFactory{informers: map[reflect.Type]*informer{}}
	p1 := f.InformerFor(&Pod{})
	p2 := f.InformerFor(&Pod{Name: "a"})
	n := f.InformerFor(&Node2{})
	if p1 != p2 || p1 == n || len(f.informers) != 2 {
		panic("type-identity: one informer per type")
	}
	if p1.objType != "*reflect.Pod" || n.objType != "*reflect.Node2" {
		panic("type-identity: String of a pointer type")
	}
	// a pointer and its element, and two defined types with the same underlying type, differ
	if reflect.TypeOf(&Pod{}) == reflect.TypeOf(Pod{}) || reflect.TypeOf(Pod{}) == reflect.TypeOf(Node2{}) {
		panic("type-identity: distinct types compare equal")
	}
	expected := reflect.TypeOf(&Pod{})
	if !acceptEvent(expected, &Pod{}) || acceptEvent(expected, &Node2{}) || acceptEvent(expected, Pod{}) {
		panic("type-identity: reflector's check")
	}
	if !acceptEvent(nil, &Node2{}) {
		panic("type-identity: no expected type accepts all")
	}
	if handlerName(&Pod{}) != pkgPath+".Pod" || handlerName(Node2{}) != pkgPath+".Node2" {
		panic("type-identity: handler name")
	}
	if handlerName((*Pod)(nil)) != "" { // a nil pointer: the pointer type, no name, no package
		panic("type-identity: handler name of a nil pointer")
	}
	if reflect.TypeOf(x{}).PkgPath() != pkgPath || reflect.TypeOf(x{}).Name() != "x" {
		panic("type-identity: PkgPath of an unexported type")
	}
	if reflect.TypeOf(0).PkgPath() != "" || reflect.TypeOf(0).Name() != "int" || reflect.TypeOf([]byte(nil)).String() != "[]uint8" {
		panic("type-identity: predeclared and composite types")
	}
	if fmt.Sprintf("%T", &Pod{}) != "*reflect.Pod" || fmt.Sprintf("%T", nil) != "<nil>" {
		panic("type-identity: %T")
	}
}
