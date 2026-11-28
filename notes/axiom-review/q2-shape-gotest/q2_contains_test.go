// Q2 widening probe (2026-11-27): Contains of an empty or inverted query, which auth's
// checkKeyInterval asks for a request whose range end is at or below its key.
package adt

import "testing"

func TestQ2ContainsEmptyInverted(t *testing.T) {
	pt := func(k string) Interval { return NewStringAffineInterval(k, k+"\x00") }
	// A user whose only permission is the point "p".
	tp := NewIntervalTree()
	tp.Insert(pt("p"), struct{}{})
	t.Logf("empty [a,a) over {p}: %v", tp.Contains(NewStringAffineInterval("a", "a")))
	t.Logf("inverted [e,b) over {p}: %v", tp.Contains(NewStringAffineInterval("e", "b")))

	// The same two intervals inserted in either order: the inverted query's answer differs.
	x := NewStringAffineInterval("c", "d")
	y := NewStringAffineInterval("d", "z")
	q := NewStringAffineInterval("e", "b")
	t1 := NewIntervalTree()
	t1.Insert(x, 1)
	t1.Insert(y, 2)
	t2 := NewIntervalTree()
	t2.Insert(y, 2)
	t2.Insert(x, 1)
	c1, c2 := t1.Contains(q), t2.Contains(q)
	t.Logf("inverted [e,b) over {[c,d),[d,z)}: inserted x then y: %v; y then x: %v", c1, c2)
	if c1 == c2 {
		t.Fatalf("expected the answer to depend on the insertion order")
	}
}
