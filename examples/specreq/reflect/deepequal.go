package reflect

// reflect.DeepEqual at the shapes the verified code compares.
//
// Mirrors:
//   - bbolt (upamanyus/bbolt@ca88bb6a8) internal/freelist/hashmap.go:184,187
//     (mergeSpans, under common.Verify: two `map[common.Pgid]struct{}` sets
//     built by idsFromFreemaps/idsFromForwardMap/idsFromBackwardMap, a panic
//     with %v of both on mismatch); translated with its body
//     (Code/go_etcd_io/bbolt/internal/freelist.lean); axiom
//     reflect.DeepEqual.wp_proof_pgidSet;
//   - etcd client/pkg/v3 types/set.go:98 (unsafeSet.Equals: two sorted
//     sort.StringSlice);
//   - k8s.io/kubernetes@878cfa6c4cc7 pkg/controller/daemon/
//     daemon_controller.go:518,651 (`*metav1.OwnerReference`), :539,684 (label
//     maps), :1330 (`*metav1.LabelSelector` against `&everything`),
//     update.go:571 (`*int32`); translated with their bodies
//     (Code/k8s_io/kubernetes/pkg/controller/daemon.lean);
//   - client-go tools/cache/mutation_detector.go:147,153 (whole cached
//     objects against their deep copies), apiserver cacher/caching_object.go:
//     365-409 (labels, annotations, finalizers, owner references);
//   - the k8s checker examples/k8s/etcd3/correctness/model.go:111-341,
//     replay.go:99 (responses, objects, errors, maps of objects); axiom
//     reflect.DeepEqual.wp_proof_k8s (Spec/reflect/DeepEqualK8s.lean);
//   - zap zapcore/field.go:202 (Field.Equals), grpc service_config.go:359.
//
// Go 1.27.3 reflect/deepequal.go: false if the dynamic types differ; a nil
// slice or map is not equal to an empty one; pointers equal if the same or
// their pointees are; structs field by field, unexported fields included;
// maps by length and every key's value; funcs equal only if both nil; floats
// by == (NaN is not equal to itself, but a slice is equal to itself, so a
// NaN in the same slice is "equal"); cycles terminate through a visited set
// of (pointer, pointer, type) for pointers, maps, slices and interfaces.
// It never panics.
//
// To prove: DeepEqual never panics and returns the deep equality above at
// each shape, including the cyclic list (which must terminate and be true).
//
// Needs R2 (a recursive walk: Kind, Len, Index, MapIndex, MapKeys, NumField,
// Field of unexported fields, Elem, IsNil, Pointer for the same-pointer and
// visited tests) and R1 (type identity); the visited set keys on addresses
// (unsafe-dependent inside reflect: the semantics can make DeepEqual a
// primitive instead).

import (
	"math"
	"reflect"
	"sort"
)

type Pgid uint64

type OwnerReference struct {
	Kind       string
	Name       string
	Controller *bool
}

type LabelSelector struct {
	MatchLabels map[string]string
}

type withUnexported struct {
	Name  string
	cache []int
}

type cell struct {
	Val  int
	Next *cell
}

// REQ reflect/deep-equal: DeepEqual is deep equality at the verified code's shapes: pgid sets
// (equal iff same keys; a nil and an empty map differ), sorted string slices (a nil and an
// empty slice differ), owner references through pointers (the same pointee values, different
// pointers: equal), label maps, a selector against `&everything`, *int32, structs with
// unexported fields, values of different dynamic types (false), NaN (false), funcs (false
// unless both nil), and a cyclic list (terminates, true).
// Users: bbolt internal/freelist/hashmap.go:184,187; etcd client/pkg types/set.go:98; k8s
// daemon_controller.go:518,539,651,684,1330, update.go:571; client-go mutation_detector.go:147;
// apiserver cacher/caching_object.go:365-409; the k8s checker model.go, replay.go.
// Assumes: nothing.
// Specs: none yet; needs R1 and R2, or DeepEqual as a primitive (doc.go).
func ReqDeepEqual() {
	a := map[Pgid]struct{}{3: {}, 4: {}}
	b := map[Pgid]struct{}{4: {}, 3: {}}
	if !reflect.DeepEqual(a, b) || reflect.DeepEqual(a, map[Pgid]struct{}{3: {}}) {
		panic("deep-equal: pgid sets")
	}
	if reflect.DeepEqual(map[Pgid]struct{}{}, map[Pgid]struct{}(nil)) {
		panic("deep-equal: a nil map is not an empty one")
	}
	s1, s2 := sort.StringSlice{"b", "a"}, sort.StringSlice{"a", "b"}
	s1.Sort()
	if !reflect.DeepEqual(s1, s2) || reflect.DeepEqual(sort.StringSlice{}, sort.StringSlice(nil)) {
		panic("deep-equal: string slices")
	}
	if reflect.DeepEqual(s2, []string{"a", "b"}) {
		panic("deep-equal: different named types are not deeply equal")
	}
	t1, t2 := true, true
	r1 := &OwnerReference{Kind: "DaemonSet", Name: "ds", Controller: &t1}
	r2 := &OwnerReference{Kind: "DaemonSet", Name: "ds", Controller: &t2}
	if !reflect.DeepEqual(r1, r2) || reflect.DeepEqual(r1, (*OwnerReference)(nil)) {
		panic("deep-equal: owner references")
	}
	everything := LabelSelector{}
	if !reflect.DeepEqual(&LabelSelector{}, &everything) || reflect.DeepEqual(&LabelSelector{MatchLabels: map[string]string{}}, &everything) {
		panic("deep-equal: the selector that selects everything")
	}
	var n1, n2 int32 = 2, 2
	if !reflect.DeepEqual(&n1, &n2) || reflect.DeepEqual(&n1, (*int32)(nil)) {
		panic("deep-equal: *int32")
	}
	if !reflect.DeepEqual(withUnexported{"x", []int{1}}, withUnexported{"x", []int{1}}) ||
		reflect.DeepEqual(withUnexported{"x", []int{1}}, withUnexported{"x", []int{2}}) {
		panic("deep-equal: unexported fields are compared")
	}
	if reflect.DeepEqual(any(int64(1)), any(1)) || !reflect.DeepEqual(nil, nil) || reflect.DeepEqual(nil, (*int32)(nil)) {
		panic("deep-equal: dynamic types")
	}
	if reflect.DeepEqual(math.NaN(), math.NaN()) {
		panic("deep-equal: NaN")
	}
	nan := []float64{math.NaN()}
	if !reflect.DeepEqual(nan, nan) {
		panic("deep-equal: the same slice is equal to itself")
	}
	f := func() {}
	if reflect.DeepEqual(f, f) || !reflect.DeepEqual((func())(nil), (func())(nil)) {
		panic("deep-equal: funcs")
	}
	c1 := &cell{Val: 1}
	c1.Next = c1
	c2 := &cell{Val: 1}
	c2.Next = c2
	if !reflect.DeepEqual(c1, c2) {
		panic("deep-equal: cycles")
	}
}
