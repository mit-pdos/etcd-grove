package reflect

// New, Zero and Set through pointers, and the interface assertion of the
// result: how the apiserver's store makes and fills objects of a type it
// knows only at run time.
//
// Mirrors:
//   - k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/pkg/storage/etcd3/
//     store.go:1181-1191 (stateFromEtcdResponse: `if u, ok :=
//     v.Addr().Interface().(runtime.Unstructured); ok { ... } else {
//     state.obj = reflect.New(v.Type()).Interface().(runtime.Object) }`, with
//     v the Elem of the caller's out pointer) and :639-654 (getNewItemFunc:
//     `elem := v.Type().Elem(); return reflect.New(elem).Interface().(runtime.Object)`);
//   - k8s.io/apimachinery@v0.0.0-20261021173754-0b7d352f711c/pkg/runtime/
//     helper.go:196-202 (SetZeroValue: EnforcePtr, then
//     `v.Set(reflect.Zero(v.Type()))`), which the store calls on a miss;
//   - apiserver pkg/storage/cacher/cacher.go:724,726 (`objVal.Set(reflect.ValueOf(obj).Elem())`,
//     `objVal.Set(reflect.Zero(objVal.Type()))`): copy a cached object into
//     the caller's;
//   - Go 1.27.3 net/rpc/server.go:561-582 (readRequest: `reflect.New(argType.Elem())`)
//     and flag/flag.go:542-562 (isZeroValue: `reflect.New(typ.Elem())` or Zero).
// stateFromEtcdResponse, getNewItemFunc and SetZeroValue are translated with
// their bodies (Code/k8s_io/apiserver/pkg/storage/etcd3.lean,
// Code/k8s_io/apimachinery/pkg/runtime.lean).
//
// Go's panics: Set on a value that is not addressable (ValueOf(x) of a
// non-pointer) panics "reflect: reflect.Value.Set using unaddressable
// value"; Set of a value of another type "reflect.Set: value of type
// *reflect.Pod2 is not assignable to type reflect.Pod2". Addr of an
// unaddressable value panics too.
//
// To prove: the store's uses do not panic, because every value they Set or
// Addr is the Elem of a pointer, and every value they Set into has the type of
// the value set; New(t) gives a fresh pointer to t's zero value whose
// Interface() asserts to the interface t's pointer implements; after Set,
// the caller's variable holds the new value (the pointer is the caller's).
//
// Needs R1 (Elem of a pointer type, method sets for the assertion) and R2
// (ValueOf, Elem, Addr, Interface, New, Zero, Set and its addressability
// and assignability checks; a Value aliasing the caller's memory).

import "reflect"

// Object stands for runtime.Object; Unstructured for runtime.Unstructured.
type Object interface{ GetName() string }
type Unstructured interface {
	Object
	NewEmptyInstance() Unstructured
}

type Pod2 struct {
	Name   string
	Labels map[string]string
}

func (p *Pod2) GetName() string { return p.Name }

type Unstr struct{ Object map[string]any }

func (u *Unstr) GetName() string                { return "" }
func (u *Unstr) NewEmptyInstance() Unstructured { return &Unstr{} }

// newObjFor is stateFromEtcdResponse's allocation (store.go:1187-1191).
func newObjFor(v reflect.Value) Object {
	if u, ok := v.Addr().Interface().(Unstructured); ok {
		return u.NewEmptyInstance()
	}
	return reflect.New(v.Type()).Interface().(Object)
}

// setZeroValue is runtime.SetZeroValue (helper.go:196).
func setZeroValue(objPtr Object) string {
	v, err := enforcePtr(objPtr)
	if err != "" {
		return err
	}
	v.Set(reflect.Zero(v.Type()))
	return ""
}

// copyInto is the cacher's Get (cacher.go:719-727): copy the cached object into the caller's.
func copyInto(objPtr Object, cached Object, found bool) {
	objVal, err := enforcePtr(objPtr)
	if err != "" {
		panic("ptr-set: " + err)
	}
	if found {
		objVal.Set(reflect.ValueOf(cached).Elem())
	} else {
		objVal.Set(reflect.Zero(objVal.Type()))
	}
}

// REQ reflect/ptr-set: New of the run-time type gives a fresh zero object that asserts to
// Object (and the Unstructured path is taken for unstructured objects); SetZeroValue zeroes the
// caller's object through its pointer; the cacher's copy writes the cached object into the
// caller's variable (a copy: later writes to one do not show in the other's fields).
// Users: apiserver storage/etcd3/store.go:650-653,1187-1191; apimachinery runtime/helper.go:201;
// storage/cacher/cacher.go:724,726; net/rpc server.go:561-582; flag.go:542-562.
// Assumes: nothing.
// Specs: none yet; needs R1 (Elem, method sets) and R2 (New, Zero, Set, Addr, Interface) (doc.go).
func ReqPtrSet() {
	out := &Pod2{Name: "old"}
	o := newObjFor(reflect.ValueOf(out).Elem())
	p, ok := o.(*Pod2)
	if !ok || p == out || p.Name != "" || p.Labels != nil {
		panic("ptr-set: New of the run-time type")
	}
	if _, ok := newObjFor(reflect.ValueOf(&Unstr{}).Elem()).(*Unstr); !ok {
		panic("ptr-set: the Unstructured path")
	}
	// getNewItemFunc: the element type of a slice type
	items := reflect.ValueOf(&[]Pod2{}).Elem()
	if _, ok := reflect.New(items.Type().Elem()).Interface().(Object); !ok {
		panic("ptr-set: New of a slice's element type")
	}
	out.Labels = map[string]string{"a": "b"}
	if err := setZeroValue(out); err != "" || out.Name != "" || out.Labels != nil {
		panic("ptr-set: SetZeroValue")
	}
	cached := &Pod2{Name: "cached"}
	copyInto(out, cached, true)
	if out.Name != "cached" || out == cached {
		panic("ptr-set: copy of the cached object")
	}
	cached.Name = "changed"
	if out.Name != "cached" {
		panic("ptr-set: Set copies the struct")
	}
	copyInto(out, nil, false)
	if out.Name != "" {
		panic("ptr-set: not found zeroes")
	}
}

// REQ reflect/ptr-set (panics): Set on ValueOf of a non-pointer panics "reflect:
// reflect.Value.Set using unaddressable value".
// Specs: none yet.
func MustPanicSetUnaddressable() {
	reflect.ValueOf(Pod2{}).Set(reflect.ValueOf(Pod2{Name: "x"}))
}

// REQ reflect/ptr-set (panics): Set of a *Pod2 into a Pod2 panics "reflect.Set: value of type
// *reflect.Pod2 is not assignable to type reflect.Pod2" (the cacher's copy with the Elem
// forgotten).
// Specs: none yet.
func MustPanicSetWrongType() {
	reflect.ValueOf(&Pod2{}).Elem().Set(reflect.ValueOf(&Pod2{}))
}
