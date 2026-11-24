package reflect

// Types built at run time (ArrayOf, SliceOf, PointerTo, TypeFor) and values
// of them: otel's attribute sets.
//
// Mirrors go.opentelemetry.io/otel@v1.47.0 attribute/set.go:
//   - :404-410 (computeDataReflect, for a set of more than 10 attributes:
//     `at := reflect.New(reflect.ArrayOf(len(kvs), keyValueType)).Elem()`,
//     `*at.Index(i).Addr().Interface().(*KeyValue) = keyValue`, `return
//     at.Interface()`: an array value of a type built at run time, held in an
//     `any`); the cases up to 10 are `[N]KeyValue(kvs)` conversions;
//   - :97-140 (Len, Get, Value: `reflect.ValueOf(l.data)`, Len, `Index(idx).Interface().(KeyValue)`,
//     inside sort.Search);
//   - :182-192 (Equals: `l.data == o.data`, == of two interfaces holding
//     arrays of the built type: equal iff same array type and elements);
//   - `keyValueType = reflect.TypeFor[KeyValue]()` (attribute.lean's initializer).
// etcd builds attribute sets for every traced request (otel's tracing of
// grpc, the server's spans); the scalar constructors are translated with
// their bodies (Code/go_opentelemetry_io/otel/attribute.lean), the set's
// methods names-only. Also: encoding/json/v2's `reflect.SliceOf(t.Key())`
// (arshal_default.go:913-940), `reflect.PointerTo(t)` (arshal_methods.go:
// 417-429, jsonwalk.go), net/rpc's PointerTo hint (rpcregister.go), k8s
// apimachinery runtime/converter.go:769 (SliceOf).
//
// To prove: ArrayOf(n, T) for the same n and T is the same type each time
// (so two sets of the same attributes are ==, and sets of different sizes
// are not), its values are comparable when T is, Index/Addr/Interface give
// a pointer into the array, and Get/Value read back what was stored.
//
// Needs R1 (type construction: ArrayOf, SliceOf, PointerTo, TypeFor;
// identity of constructed types with each other and with the static [N]T;
// Comparable) and R2 (New, Elem, Index, Addr, Interface, Len; == of
// interface-held arrays).

import (
	"reflect"
	"sort"
	"strconv"
)

type Key string

type KeyValue struct {
	Key   Key
	Value int64
}

var keyValueType = reflect.TypeFor[KeyValue]()

// attrSet is attribute.Set, minimized: data holds an array of KeyValue, sorted by key.
type attrSet struct{ data any }

func computeDataReflect(kvs []KeyValue) any {
	at := reflect.New(reflect.ArrayOf(len(kvs), keyValueType)).Elem()
	for i, keyValue := range kvs {
		*at.Index(i).Addr().Interface().(*KeyValue) = keyValue
	}
	return at.Interface()
}

func newAttrSet(kvs []KeyValue) attrSet {
	sort.Slice(kvs, func(i, j int) bool { return kvs[i].Key < kvs[j].Key })
	return attrSet{data: computeDataReflect(kvs)}
}

func (l attrSet) Len() int { return reflect.ValueOf(l.data).Len() }

func (l attrSet) Value(k Key) (int64, bool) {
	rValue := reflect.ValueOf(l.data)
	vlen := rValue.Len()
	idx := sort.Search(vlen, func(idx int) bool {
		return rValue.Index(idx).Interface().(KeyValue).Key >= k
	})
	if idx >= vlen {
		return 0, false
	}
	keyValue := rValue.Index(idx).Interface().(KeyValue)
	if k == keyValue.Key {
		return keyValue.Value, true
	}
	return 0, false
}

func (l attrSet) Equals(o attrSet) bool { return l.data == o.data }

func manyKVs(n int, shift int64) []KeyValue {
	var kvs []KeyValue
	for i := n - 1; i >= 0; i-- {
		kvs = append(kvs, KeyValue{Key: Key("k" + strconv.Itoa(10+i)), Value: int64(i) + shift})
	}
	return kvs
}

// REQ reflect/type-construct: a set of 12 attributes built by ArrayOf finds each value by key,
// equals a set of the same attributes built separately (the constructed array types are
// identical, and identical to the static [12]KeyValue), and differs from a set with another
// value or another size; SliceOf and PointerTo build the types the static syntax names.
// Users: otel attribute/set.go:97-140,182-192,404-410; encoding/json/v2 arshal_default.go:
// 913-940, arshal_methods.go:417-429; net/rpc server.go:267; k8s runtime/converter.go:769.
// Assumes: nothing.
// Specs: none yet; needs R1 (type construction) and R2 (doc.go).
func ReqTypeConstruct() {
	s1 := newAttrSet(manyKVs(12, 0))
	s2 := newAttrSet(manyKVs(12, 0))
	if s1.Len() != 12 {
		panic("type-construct: Len")
	}
	if v, ok := s1.Value("k15"); !ok || v != 5 {
		panic("type-construct: Value")
	}
	if _, ok := s1.Value("k99"); ok {
		panic("type-construct: a missing key")
	}
	if !s1.Equals(s2) || s1.Equals(newAttrSet(manyKVs(12, 1))) || s1.Equals(newAttrSet(manyKVs(11, 0))) {
		panic("type-construct: Equals")
	}
	if reflect.TypeOf(s1.data) != reflect.TypeOf([12]KeyValue{}) || reflect.TypeOf(s1.data).String() != "[12]reflect.KeyValue" {
		panic("type-construct: ArrayOf is the static array type")
	}
	if reflect.SliceOf(keyValueType) != reflect.TypeOf([]KeyValue(nil)) || reflect.PointerTo(keyValueType) != reflect.TypeOf((*KeyValue)(nil)) {
		panic("type-construct: SliceOf, PointerTo")
	}
	if !reflect.ArrayOf(3, keyValueType).Comparable() || reflect.SliceOf(keyValueType).Comparable() {
		panic("type-construct: Comparable")
	}
}
