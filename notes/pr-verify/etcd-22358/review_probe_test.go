package adt

import (
	"math"
	"testing"
)

func TestReviewProbe(t *testing.T) {
	M := int64(math.MaxInt64)
	// 1. point at MaxInt64 inserted, then stabbed with itself
	ivt := NewIntervalTree()
	ivt.Insert(NewInt64Point(M), "pM")
	ivt.Insert(NewInt64Point(5), "p5")
	t.Logf("Stab(Point(M)) on tree {Point(M),Point(5)} = %d results; Intersects=%v; Find=%v",
		len(ivt.Stab(NewInt64Point(M))), ivt.Intersects(NewInt64Point(M)), ivt.Find(NewInt64Point(M)) != nil)
	t.Logf("Stab(Point(5)) = %d results", len(ivt.Stab(NewInt64Point(5))))
	// 2. wide interval covering up to M (exclusive) vs point M
	ivt2 := NewIntervalTree()
	ivt2.Insert(NewInt64Interval(math.MinInt64, M), "all")
	t.Logf("Stab(Point(M)) on {[Min,M)} = %d; Stab(Point(M-1)) = %d", len(ivt2.Stab(NewInt64Point(M))), len(ivt2.Stab(NewInt64Point(M-1))))
	// 3. a generic empty interval [a,a) DOES match in this tree
	ivt3 := NewIntervalTree()
	ivt3.Insert(NewInt64Interval(0, 10), "0-10")
	t.Logf("Stab([5,5)) on {[0,10)} = %d; Intersects([5,5))=%v", len(ivt3.Stab(NewInt64Interval(5, 5))), ivt3.Intersects(NewInt64Interval(5, 5)))
	ivt4 := NewIntervalTree()
	ivt4.Insert(NewInt64Interval(5, 5), "empty")
	t.Logf("Stab(Point(5)) on {[5,5)} = %d; Stab([0,10)) on {[5,5)} = %d", len(ivt4.Stab(NewInt64Point(5))), len(ivt4.Stab(NewInt64Interval(0, 10))))
	// 4. Compare orientation for [M,M)
	pm := NewInt64Point(M)
	x := NewInt64Interval(0, 10)
	t.Logf("pm.Compare(x)=%d x.Compare(pm)=%d", pm.Compare(&x), x.Compare(&pm))
	// 5. extremes of Compare
	t.Logf("Max.Compare(Min)=%d Min.Compare(Max)=%d Max.Compare(-1)=%d 0.Compare(Min)=%d Min.Compare(1)=%d",
		Int64Comparable(M).Compare(Int64Comparable(math.MinInt64)), Int64Comparable(math.MinInt64).Compare(Int64Comparable(M)),
		Int64Comparable(M).Compare(Int64Comparable(-1)), Int64Comparable(0).Compare(Int64Comparable(math.MinInt64)),
		Int64Comparable(math.MinInt64).Compare(Int64Comparable(1)))
	// 6. same class: affine points at the top element "" (Begin > End)
	sp := NewStringAffinePoint("")
	bp := NewBytesAffinePoint(nil)
	t.Logf("StringAffinePoint(\"\"): Begin.Compare(End)=%d; BytesAffinePoint(nil): Begin.Compare(End)=%d", sp.Begin.Compare(sp.End), bp.Begin.Compare(bp.End))
	ivt5 := NewIntervalTree()
	ivt5.Insert(NewStringAffineInterval("a", ""), "a-inf")
	t.Logf("Stab(StringAffinePoint(\"\")) on {[a,+inf)} = %d", len(ivt5.Stab(sp)))
}
