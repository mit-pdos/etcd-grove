package correctness

// Stage 7g evidence (notes/k8s-7g-scope.md, the trust-boundary spec of cmp.Diff at
// []eventReference): cmp.Diff returns "" exactly when the two slices are equal element by
// element (==) and both nil or both non-nil (a nil and an empty slice differ: toEventReference
// always makes a non-nil slice), and does not panic on the unexported type.

import (
	"math/rand"
	"reflect"
	"slices"
	"testing"

	"github.com/google/go-cmp/cmp"
	"k8s.io/apimachinery/pkg/watch"
)

func TestCmpDiffEventRefs(t *testing.T) {
	a := eventReference{Key: "/objs/ns-1/pod-1", Type: watch.Added, ResourceVersion: 4}
	b := eventReference{Key: "/objs/ns-1/pod-1", Type: watch.Modified, ResourceVersion: 4}
	c := eventReference{Key: "/objs/ns-1/pod-1", Type: watch.Added, ResourceVersion: 5}
	cases := []struct {
		x, y []eventReference
		eq   bool
	}{
		{nil, nil, true},
		{nil, []eventReference{}, false},
		{[]eventReference{}, nil, false},
		{[]eventReference{}, []eventReference{}, true},
		{[]eventReference{a}, []eventReference{a}, true},
		{[]eventReference{a, c}, []eventReference{a, c}, true},
		{[]eventReference{a}, []eventReference{b}, false},
		{[]eventReference{a}, []eventReference{c}, false},
		{[]eventReference{a}, []eventReference{a, a}, false},
		{[]eventReference{a, c}, []eventReference{c, a}, false},
		{nil, []eventReference{a}, false},
	}
	for i, tc := range cases {
		d := cmp.Diff(tc.x, tc.y)
		if (d == "") != tc.eq {
			t.Errorf("case %d: Diff %q, want equal %v", i, d, tc.eq)
		}
	}
}

// The spec's claim on random pairs (Spec/github_com/google/go_cmp/cmp/Diff.lean, cmp.Diff.spec_eventRefs):
// with no options, cmp.Diff of two []eventReference is "" exactly when both are nil or both
// non-nil and they are equal element by element (Go's ==); it never panics (its own
// consistency check, `(d == "") != s.result.Equal()`, holds). Neither eventReference nor
// watch.EventType has an Equal method (which cmp.Equal would call instead of comparing fields),
// and eventReference has no unexported field (on which cmp panics).
func TestCmpDiffEventRefsRandom(t *testing.T) {
	for _, ty := range []reflect.Type{reflect.TypeOf(eventReference{}), reflect.TypeOf(watch.Added)} {
		if _, ok := ty.MethodByName("Equal"); ok {
			t.Errorf("%v has an Equal method", ty)
		}
		if _, ok := reflect.PointerTo(ty).MethodByName("Equal"); ok {
			t.Errorf("*%v has an Equal method", ty)
		}
	}
	et := reflect.TypeOf(eventReference{})
	for i := 0; i < et.NumField(); i++ {
		if !et.Field(i).IsExported() {
			t.Errorf("unexported field %s", et.Field(i).Name)
		}
	}
	r := rand.New(rand.NewSource(11))
	keys := []string{"", "/objs/a", "/objs/b"}
	types := []watch.EventType{watch.Added, watch.Modified, watch.Deleted}
	ref := func() eventReference {
		return eventReference{Key: keys[r.Intn(3)], Type: types[r.Intn(3)], ResourceVersion: uint64(r.Intn(3))}
	}
	gen := func() []eventReference {
		if r.Intn(5) == 0 {
			return nil
		}
		s := make([]eventReference, 0, r.Intn(4))
		for j := r.Intn(3); j > 0; j-- {
			s = append(s, ref())
		}
		return s
	}
	for i := 0; i < 20000; i++ {
		x := gen()
		y := slices.Clone(x)
		if r.Intn(2) == 0 {
			y = gen()
		} else if len(y) > 0 && r.Intn(2) == 0 {
			y[r.Intn(len(y))] = ref()
		}
		want := (x == nil) == (y == nil) && slices.Equal(x, y)
		if d := cmp.Diff(x, y); (d == "") != want {
			t.Fatalf("Diff(%v, %v) = %q, want equal %v", x, y, d, want)
		}
	}
}
