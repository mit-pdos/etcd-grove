package correctness

// Stage 7g evidence (notes/k8s-7g-scope.md, the trust-boundary spec of cmp.Diff at
// []eventReference): cmp.Diff returns "" exactly when the two slices are equal element by
// element (==) and both nil or both non-nil (a nil and an empty slice differ: toEventReference
// always makes a non-nil slice), and does not panic on the unexported type.

import (
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
