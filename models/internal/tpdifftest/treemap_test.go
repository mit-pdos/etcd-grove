package tpdifftest_test

import (
	"math/rand"
	"sort"
	"testing"

	"github.com/emirpasic/gods/maps/treemap"
)

// The gods treemap model (models/gods) against gods v1.18.1: random sequences of the operations
// the kits use (NewWith, Put, Get, Select, Iterator, Next, Value), each outcome written to the
// transcript (run.sh compares the real library's with the model's) and checked against a
// reference (a sorted list) in either build.
//
// Keys are {K, Tag} compared by K only (a total preorder, as the model's claim requires), so that
// a Put of an existing K replacing the entry's key is observable (Select's predicate sees the
// keys). Small K ranges make collisions common.

type tmKey struct{ K, Tag int }

func tmCompare(a, b interface{}) int {
	x, y := a.(tmKey).K, b.(tmKey).K
	switch {
	case x < y:
		return -1
	case x > y:
		return 1
	}
	return 0
}

type tmEntry struct {
	key tmKey
	val int
}

// tmRef is the reference: the entries sorted by K.
type tmRef []tmEntry

func (r *tmRef) put(k tmKey, v int) {
	for i := range *r {
		if (*r)[i].key.K == k.K {
			(*r)[i] = tmEntry{k, v}
			return
		}
	}
	*r = append(*r, tmEntry{k, v})
	sort.Slice(*r, func(i, j int) bool { return (*r)[i].key.K < (*r)[j].key.K })
}

func (r tmRef) get(k int) (int, bool) {
	for _, e := range r {
		if e.key.K == k {
			return e.val, true
		}
	}
	return 0, false
}

// tmPred is a Select predicate: SwiftPaxos's SCAN (K in [lo, hi]), a value test, all, none.
func tmPred(rng *rand.Rand, keyRange int) (string, func(k tmKey, v int) bool) {
	switch rng.Intn(5) {
	case 0, 1:
		lo := rng.Intn(keyRange+2) - 1
		hi := lo + rng.Intn(keyRange+1) - 1
		return "range", func(k tmKey, v int) bool { return k.K >= lo && k.K <= hi }
	case 2:
		return "odd", func(k tmKey, v int) bool { return v%2 != 0 }
	case 3:
		return "all", func(k tmKey, v int) bool { return true }
	}
	return "none", func(k tmKey, v int) bool { return false }
}

// tmIterate walks it to its end, recording each value, then checks that Next stays false and
// Value panics past the end. Returns the values.
func tmIterate(t *testing.T, tr *transcript, it treemap.Iterator) []int {
	var vals []int
	for it.Next() {
		vals = append(vals, it.Value().(int))
	}
	tr.printf("  iter %v", vals)
	again := it.Next()
	pv := panics(func() { it.Value() })
	tr.printf("  past end: next=%v value-panics=%v", again, pv)
	if again || !pv {
		t.Errorf("past the end: Next %v, Value panics %v", again, pv)
	}
	return vals
}

func TestTreemapRandom(t *testing.T) {
	tr := newTranscript("treemap")
	rng := rand.New(rand.NewSource(1))
	const seqs = 4000
	ops := 0
	for s := 0; s < seqs; s++ {
		keyRange := 1 + rng.Intn(24)
		n := rng.Intn(80)
		tr.printf("seq %d keys %d ops %d", s, keyRange, n)
		m := treemap.NewWith(tmCompare)
		var ref tmRef
		// a fresh map's iterator: Value before Next panics, Next is false
		it0 := m.Iterator()
		tr.printf(" empty: value-panics=%v next=%v", panics(func() { it0.Value() }), it0.Next())
		for i := 0; i < n; i++ {
			ops++
			switch op := rng.Intn(10); {
			case op < 4:
				k := tmKey{rng.Intn(keyRange), rng.Intn(1000)}
				v := rng.Intn(1000)
				m.Put(k, v)
				ref.put(k, v)
				tr.printf(" put %v %d", k, v)
			case op < 7:
				k := rng.Intn(keyRange+2) - 1
				v, ok := m.Get(tmKey{k, -1})
				tr.printf(" get %d = %v %v", k, v, ok)
				rv, rok := ref.get(k)
				if ok != rok || (ok && v.(int) != rv) || (!ok && v != nil) {
					t.Fatalf("seq %d: Get(%d) = %v, %v; reference %v, %v", s, k, v, ok, rv, rok)
				}
			case op < 9:
				name, p := tmPred(rng, keyRange)
				var seen []tmKey
				sel := m.Select(func(k, v interface{}) bool {
					seen = append(seen, k.(tmKey))
					return p(k.(tmKey), v.(int))
				})
				tr.printf(" select %s: f saw %v", name, seen)
				var want []int
				var wantSeen []tmKey
				for _, e := range ref {
					wantSeen = append(wantSeen, e.key)
					if p(e.key, e.val) {
						want = append(want, e.val)
					}
				}
				if !equalKeys(seen, wantSeen) {
					t.Fatalf("seq %d: Select's f saw %v; reference %v", s, seen, wantSeen)
				}
				it := sel.Iterator()
				pv := panics(func() { it.Value() })
				tr.printf("  value before next panics=%v", pv)
				if !pv {
					t.Errorf("Value before Next did not panic")
				}
				got := tmIterate(t, tr, it)
				if !equalInts(got, want) {
					t.Fatalf("seq %d: Select(%s) iterates %v; reference %v", s, name, got, want)
				}
				// the selected map is a map of its own, with the comparator
				k := tmKey{rng.Intn(keyRange), 7}
				sel.Put(k, 1)
				v, ok := sel.Get(tmKey{k.K, 0})
				ov, ook := m.Get(tmKey{k.K, 0})
				tr.printf("  sel put %v: sel get %v %v, map get %v %v", k, v, ok, ov, ook)
			default:
				got := tmIterate(t, tr, m.Iterator())
				var want []int
				for _, e := range ref {
					want = append(want, e.val)
				}
				if !equalInts(got, want) {
					t.Fatalf("seq %d: iterates %v; reference %v", s, got, want)
				}
			}
		}
	}
	tr.printf("sequences %d operations %d", seqs, ops)
	t.Logf("treemap: %d sequences, %d operations", seqs, ops)
	tr.save(t)
}

// TestTreemapComparatorPanics: a key the comparator rejects panics at the first Put into an empty
// map (gods asserts the key's type there by calling comparator(k, k)), at any Put or Get on a
// non-empty map, and not at a Get on an empty map (no comparison).
func TestTreemapComparatorPanics(t *testing.T) {
	tr := newTranscript("treemap-panics")
	m := treemap.NewWith(tmCompare)
	tr.printf("get on empty with a bad key panics=%v", panics(func() { m.Get("bad") }))
	tr.printf("put on empty with a bad key panics=%v", panics(func() { m.Put("bad", 1) }))
	it := m.Iterator()
	tr.printf("after it, next=%v", it.Next())
	m.Put(tmKey{1, 0}, 1)
	tr.printf("put on non-empty with a bad key panics=%v", panics(func() { m.Put("bad", 2) }))
	tr.printf("get on non-empty with a bad key panics=%v", panics(func() { m.Get("bad") }))
	v, ok := m.Get(tmKey{1, 0})
	tr.printf("get 1 = %v %v", v, ok)
	tr.save(t)
}

func equalInts(a, b []int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func equalKeys(a, b []tmKey) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
