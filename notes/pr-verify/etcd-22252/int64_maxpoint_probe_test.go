// Probe for etcd#22252 (review, 2026-10-17): with the fixed Int64Comparable.Compare but the
// unfixed NewInt64Point, NewInt64Point(MaxInt64) is [MaxInt64, MinInt64) (Begin > End).
// Randomized check of the interval tree's operations and invariants against brute force, run
// once with #22252's point constructor and once with #22358's ([MaxInt64, MaxInt64)); the
// Compare of both PRs is the same, so the second run is #22358's behaviour.

package adt

import (
	"math"
	"math/rand"
	"sort"
	"testing"
)

type mpIvl struct{ b, e int64 }

func mpPoint22252(a int64) mpIvl { return mpIvl{a, a + 1} } // what NewInt64Point does at head
func mpPoint22358(a int64) mpIvl {
	if a == math.MaxInt64 {
		return mpIvl{a, a}
	}
	return mpIvl{a, a + 1}
}

func (x mpIvl) ivl() Interval { return NewInt64Interval(x.b, x.e) }

// As sets of integers: [b, e) is empty when b >= e.
func mpOverlap(x, y mpIvl) bool {
	if x.b >= x.e || y.b >= y.e {
		return false
	}
	return x.b < y.e && y.b < x.e
}

func mpLex(x, y mpIvl) bool { return x.b < y.b || (x.b == y.b && x.e < y.e) }

// Checks BST order, parent links, max augmentation, red-black properties and count.
func mpCheckTree(t *testing.T, ivt *intervalTree, live []mpIvl) bool {
	s := ivt.sentinel
	var inorder []mpIvl
	var walk func(x *intervalNode) (int64, int) // returns subtree max End, black height
	ok := true
	walk = func(x *intervalNode) (int64, int) {
		if x == s {
			return math.MinInt64, 1
		}
		lm, lh := walk(x.left)
		me := mpIvl{int64(x.iv.Ivl.Begin.(Int64Comparable)), int64(x.iv.Ivl.End.(Int64Comparable))}
		inorder = append(inorder, me)
		rm, rh := walk(x.right)
		m := me.e
		if x.left != s && lm > m {
			m = lm
		}
		if x.right != s && rm > m {
			m = rm
		}
		if int64(x.max.(Int64Comparable)) != m {
			t.Errorf("node %v: max %v, want %d", me, x.max, m)
			ok = false
		}
		if x.left != s && x.left.parent != x || x.right != s && x.right.parent != x {
			t.Errorf("node %v: bad parent link", me)
			ok = false
		}
		if x.c == red && (x.left.color(s) == red || x.right.color(s) == red) {
			t.Errorf("node %v: red with red child", me)
			ok = false
		}
		if lh != rh {
			t.Errorf("node %v: black heights %d/%d", me, lh, rh)
			ok = false
		}
		if x.c == black {
			lh++
		}
		return m, lh
	}
	walk(ivt.root)
	for i := 1; i < len(inorder); i++ {
		if mpLex(inorder[i], inorder[i-1]) {
			t.Errorf("in-order not sorted: %v", inorder)
			ok = false
			break
		}
	}
	want := append([]mpIvl(nil), live...)
	sort.Slice(want, func(i, j int) bool { return mpLex(want[i], want[j]) })
	if len(want) != len(inorder) || ivt.count != len(want) {
		t.Errorf("tree has %v (count %d), want %v", inorder, ivt.count, want)
		return false
	}
	for i := range want {
		if want[i] != inorder[i] {
			t.Errorf("tree has %v, want %v", inorder, want)
			return false
		}
	}
	return ok
}

func mpQueries(t *testing.T, ivt *intervalTree, live []mpIvl, qs []mpIvl) bool {
	ok := true
	for _, q := range qs {
		want := 0
		var ov []mpIvl
		for _, x := range live {
			if mpOverlap(q, x) {
				want++
				ov = append(ov, x)
			}
		}
		got := ivt.Stab(q.ivl())
		if len(got) != want {
			t.Errorf("live %v: Stab(%v) = %d results, want %d", live, q, len(got), want)
			ok = false
		}
		for _, g := range got {
			gx := mpIvl{int64(g.Ivl.Begin.(Int64Comparable)), int64(g.Ivl.End.(Int64Comparable))}
			if !mpOverlap(q, gx) {
				t.Errorf("live %v: Stab(%v) returned non-overlapping %v", live, q, gx)
				ok = false
			}
		}
		// Visit order: ascending Begin.
		prev := int64(math.MinInt64)
		ivt.Visit(q.ivl(), func(n *IntervalValue) bool {
			b := int64(n.Ivl.Begin.(Int64Comparable))
			if b < prev {
				t.Errorf("Visit(%v) not ascending", q)
				ok = false
			}
			prev = b
			return true
		})
		if got := ivt.Intersects(q.ivl()); got != (want > 0) {
			t.Errorf("live %v: Intersects(%v) = %v, want %v", live, q, got, want > 0)
			ok = false
		}
		if q.b < q.e {
			// Contains: q covered by the union of the stored intervals.
			sort.Slice(ov, func(i, j int) bool { return mpLex(ov[i], ov[j]) })
			cov := false
			if len(ov) > 0 && ov[0].b <= q.b {
				end := ov[0].e
				for _, x := range ov[1:] {
					if x.b > end {
						break
					}
					if x.e > end {
						end = x.e
					}
				}
				cov = end >= q.e
			}
			if got := ivt.Contains(q.ivl()); got != cov {
				t.Errorf("live %v: Contains(%v) = %v, want %v", live, q, got, cov)
				ok = false
			}
		} else if ivt.Contains(q.ivl()) {
			t.Logf("note: Contains(empty/inverted %v) = true", q)
		}
		// Find: exact match.
		present := false
		for _, x := range live {
			if x == q {
				present = true
			}
		}
		if f := ivt.Find(q.ivl()); (f != nil) != present {
			t.Errorf("live %v: Find(%v) = %v, want present=%v", live, q, f, present)
			ok = false
		}
	}
	return ok
}

func mpRun(t *testing.T, name string, point func(int64) mpIvl, seed int64) {
	vals := []int64{math.MinInt64, math.MinInt64 + 1, -1 << 62, -2, -1, 0, 1, 2, 1 << 62,
		math.MaxInt64 - 2, math.MaxInt64 - 1, math.MaxInt64}
	var cands []mpIvl
	for _, b := range vals {
		cands = append(cands, point(b))
		for _, e := range vals {
			if b < e {
				cands = append(cands, mpIvl{b, e})
			}
		}
	}
	// Queries: every candidate, plus both PRs' MaxInt64 points (whichever constructor). Other
	// empty or inverted queries ([0, 0), [1, 0)) are left out: Interval.Compare treats an empty
	// [a, a) like the point a (it overlaps [b, e) with b <= a < e) in both PRs, a pre-existing
	// quirk unrelated to MaxInt64.
	qs := append([]mpIvl(nil), cands...)
	qs = append(qs, mpIvl{math.MaxInt64, math.MaxInt64}, mpIvl{math.MaxInt64, math.MinInt64})
	maxPt := point(math.MaxInt64)
	r := rand.New(rand.NewSource(seed))
	fails := 0
	iters := 0
	for iter := 0; iter < 3000 && fails < 5; iter++ {
		iters++
		ivt := NewIntervalTree().(*intervalTree)
		var live []mpIvl
		nops := 1 + r.Intn(25)
		for k := 0; k < nops; k++ {
			var x mpIvl
			if r.Intn(4) == 0 {
				x = maxPt
			} else {
				x = cands[r.Intn(len(cands))]
			}
			if r.Intn(3) == 0 && len(live) > 0 {
				if r.Intn(2) == 0 {
					x = live[r.Intn(len(live))]
				}
				idx := -1
				for i, y := range live {
					if y == x {
						idx = i
						break
					}
				}
				got := ivt.Delete(x.ivl())
				if got != (idx >= 0) {
					t.Errorf("%s: live %v: Delete(%v) = %v", name, live, x, got)
					fails++
				}
				if idx >= 0 {
					live = append(live[:idx], live[idx+1:]...)
				}
			} else {
				ivt.Insert(x.ivl(), k)
				live = append(live, x)
			}
			if !mpCheckTree(t, ivt, live) {
				fails++
				break
			}
		}
		if !mpQueries(t, ivt, live, qs) {
			fails++
		}
		// Union into a fresh tree with a random query interval, and with the max point.
		for _, q := range []mpIvl{qs[r.Intn(len(qs))], maxPt, {math.MinInt64, math.MaxInt64}} {
			u := NewIntervalTree().(*intervalTree)
			u.Union(ivt, q.ivl())
			var want []mpIvl
			for _, x := range live {
				if mpOverlap(q, x) {
					want = append(want, x)
				}
			}
			if !mpCheckTree(t, u, want) {
				t.Errorf("%s: Union(live %v, %v) wrong", name, live, q)
				fails++
			}
		}
	}
	t.Logf("%s: %d random trees, %d failures; point(MaxInt64) = %v", name, iters, fails, maxPt)
}

func TestProbeMaxPointTree(t *testing.T) {
	t.Run("pr22252", func(t *testing.T) { mpRun(t, "pr22252", mpPoint22252, 1) })
	t.Run("pr22358", func(t *testing.T) { mpRun(t, "pr22358", mpPoint22358, 1) })
	// The real constructor is #22252's.
	if p := NewInt64Point(math.MaxInt64); int64(p.End.(Int64Comparable)) != math.MinInt64 {
		t.Fatalf("NewInt64Point(MaxInt64) = %v, expected the wrapped [MaxInt64, MinInt64)", p)
	}
}

// The observable difference between the two: the stored interval itself, and Find across
// constructors.
func TestProbeMaxPointDiff(t *testing.T) {
	ivt := NewIntervalTree()
	ivt.Insert(NewInt64Point(math.MaxInt64), "p")
	f := ivt.Find(NewInt64Point(math.MaxInt64))
	t.Logf("22252: Find(NewInt64Point(Max)) after Insert = [%v, %v)", f.Ivl.Begin, f.Ivl.End)
	t.Logf("22252: Find([Max,Max)) = %v (22358's NewInt64Point(Max) value)", ivt.Find(NewInt64Interval(math.MaxInt64, math.MaxInt64)))
	t.Logf("22252: Stab(Max point) = %d, Intersects = %v, Contains = %v",
		len(ivt.Stab(NewInt64Point(math.MaxInt64))), ivt.Intersects(NewInt64Point(math.MaxInt64)),
		ivt.Contains(NewInt64Point(math.MaxInt64)))
	ivt.Insert(NewInt64Interval(math.MinInt64, math.MaxInt64), "all")
	t.Logf("22252 with [Min,Max) stored: Stab(Max point) = %d, Contains(Max point) = %v, Intersects = %v",
		len(ivt.Stab(NewInt64Point(math.MaxInt64))), ivt.Contains(NewInt64Point(math.MaxInt64)),
		ivt.Intersects(NewInt64Point(math.MaxInt64)))
	t.Logf("22358 equivalent: Contains([Max,Max)) = %v, Stab = %d", ivt.Contains(NewInt64Interval(math.MaxInt64, math.MaxInt64)),
		len(ivt.Stab(NewInt64Interval(math.MaxInt64, math.MaxInt64))))
}
