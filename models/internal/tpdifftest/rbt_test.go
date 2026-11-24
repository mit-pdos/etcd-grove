package tpdifftest_test

import (
	"fmt"
	"math/rand"
	"sort"
	"testing"

	"github.com/emirpasic/gods/maps/treemap"
	rbt "github.com/emirpasic/gods/trees/redblacktree"
	"github.com/emirpasic/gods/utils"
)

// The gods model's one change (models/gods/trees/redblacktree/iterator.go: Next and Prev without
// goto, MODEL:) against gods v1.18.1: random red-black trees (Puts and Removes of random int keys,
// under utils.IntComparator and under the kits' comparator, SwiftPaxos's and EPaxos's
// state.KeyComparator on an int64 Key), and on each a random walk of an iterator (Next, Prev,
// Begin, End, First, Last, NextTo, PrevTo, an IteratorAt a node, and Key, Value and Node after
// every step), through the tree's own iterator and through treemap's (which calls it). Every
// step's outcome goes to the transcript (run.sh compares the real library's with the model's) and,
// but in the walks that change the tree under the iterator, is checked against a reference (the
// sorted keys and a position in them) in either build.

// rbtKey is the kits' state.Key (an int64), and rbtKeyComparator their state.KeyComparator.
type rbtKey int64

func rbtKeyComparator(a, b interface{}) int {
	aAsserted := a.(rbtKey)
	bAsserted := b.(rbtKey)
	switch {
	case aAsserted > bAsserted:
		return 1
	case aAsserted < bAsserted:
		return -1
	default:
		return 0
	}
}

// rbtCmp is one comparator, with how to make its keys from ints.
type rbtCmp struct {
	name string
	cmp  utils.Comparator
	key  func(int) interface{}
}

var rbtCmps = []rbtCmp{
	{"int", utils.IntComparator, func(i int) interface{} { return i }},
	{"kits", rbtKeyComparator, func(i int) interface{} { return rbtKey(i) }},
}

// rbtIter is what a walk drives: the tree's iterator or treemap's.
type rbtIter interface {
	Next() bool
	Prev() bool
	Begin()
	End()
	First() bool
	Last() bool
	NextTo(func(key, value interface{}) bool) bool
	PrevTo(func(key, value interface{}) bool) bool
	Key() interface{}
	Value() interface{}
}

// rbtRef is the reference iterator: the sorted keys and a position (-1 before the first, len
// past the last).
type rbtRef struct {
	keys []int
	pos  int
}

func (r *rbtRef) next() bool {
	if r.pos < len(r.keys) {
		r.pos++
	}
	return r.pos < len(r.keys)
}

func (r *rbtRef) prev() bool {
	if r.pos >= 0 {
		r.pos--
	}
	return r.pos >= 0
}

// rbtStep makes one random step of the walk on it (and ref, if not nil) and returns its text;
// with ref it checks the step's result and the current key and value against the reference.
func rbtStep(t *testing.T, rng *rand.Rand, c rbtCmp, it rbtIter, ref *rbtRef, vals map[int]int) string {
	var name string
	var res bool
	var want bool
	switch op := rng.Intn(14); {
	case op < 5:
		name, res = "next", it.Next()
		if ref != nil {
			want = ref.next()
		}
	case op < 9:
		name, res = "prev", it.Prev()
		if ref != nil {
			want = ref.prev()
		}
	case op == 9:
		name = "begin"
		it.Begin()
		if ref != nil {
			ref.pos = -1
		}
	case op == 10:
		name = "end"
		it.End()
		if ref != nil {
			ref.pos = len(ref.keys)
		}
	case op == 11:
		name, res = "first", it.First()
		if ref != nil {
			ref.pos = -1
			want = ref.next()
		}
	case op == 12:
		name, res = "last", it.Last()
		if ref != nil {
			ref.pos = len(ref.keys)
			want = ref.prev()
		}
	default:
		// NextTo/PrevTo the next key divisible by d (Next/Prev in a loop)
		d := 1 + rng.Intn(4)
		f := func(k, v interface{}) bool { return rbtInt(k)%d == 0 }
		if rng.Intn(2) == 0 {
			name, res = fmt.Sprintf("nextto %d", d), it.NextTo(f)
			if ref != nil {
				want = false
				for ref.next() {
					if ref.keys[ref.pos]%d == 0 {
						want = true
						break
					}
				}
			}
		} else {
			name, res = fmt.Sprintf("prevto %d", d), it.PrevTo(f)
			if ref != nil {
				want = false
				for ref.prev() {
					if ref.keys[ref.pos]%d == 0 {
						want = true
						break
					}
				}
			}
		}
	}
	k := outcome(func() { name += fmt.Sprintf(" key %v", it.Key()) })
	v := outcome(func() { name += fmt.Sprintf(" value %v", it.Value()) })
	s := fmt.Sprintf("%s = %v [%s %s]", name, res, k, v)
	if ref != nil {
		isMove := name != "begin" && name != "end"
		if isMove && res != want {
			t.Fatalf("%s (%s): %s; reference %v at %d of %v", c.name, name, s, want, ref.pos, ref.keys)
		}
		inside := ref.pos >= 0 && ref.pos < len(ref.keys)
		if inside != (k == "ok") || inside != (v == "ok") {
			t.Fatalf("%s: %s; reference position %d of %v", c.name, s, ref.pos, ref.keys)
		}
		if inside {
			if got := rbtInt(it.Key()); got != ref.keys[ref.pos] {
				t.Fatalf("%s: key %d; reference %d", c.name, got, ref.keys[ref.pos])
			}
			if got := it.Value().(int); got != vals[ref.keys[ref.pos]] {
				t.Fatalf("%s: value %d; reference %d", c.name, got, vals[ref.keys[ref.pos]])
			}
		}
	}
	return s
}

func rbtInt(k interface{}) int {
	switch x := k.(type) {
	case int:
		return x
	case rbtKey:
		return int(x)
	}
	panic(fmt.Sprintf("key %T", k))
}

func TestRbtIteratorRandom(t *testing.T) {
	tr := newTranscript("rbt-iterator")
	rng := rand.New(rand.NewSource(2))
	const trees = 3000
	steps, puts, removes, mutated := 0, 0, 0, 0
	for s := 0; s < trees; s++ {
		c := rbtCmps[rng.Intn(len(rbtCmps))]
		keyRange := 1 + rng.Intn(64)
		n := rng.Intn(120)
		tree := rbt.NewWith(c.cmp)
		vals := map[int]int{}
		var ops []string
		for i := 0; i < n; i++ {
			k := rng.Intn(keyRange*2+1) - keyRange
			if rng.Intn(3) == 0 {
				tree.Remove(c.key(k))
				delete(vals, k)
				ops = append(ops, fmt.Sprintf("-%d", k))
				removes++
			} else {
				v := rng.Intn(1000)
				tree.Put(c.key(k), v)
				vals[k] = v
				ops = append(ops, fmt.Sprintf("+%d", k))
				puts++
			}
		}
		var keys []int
		for k := range vals {
			keys = append(keys, k)
		}
		sort.Ints(keys)
		tr.printf("tree %d %s: %v size %d", s, c.name, ops, tree.Size())
		if tree.Size() != len(keys) {
			t.Fatalf("tree %d: size %d; reference %d", s, tree.Size(), len(keys))
		}
		// the whole tree, in order and in reverse (Keys/Values call Next)
		tr.printf(" keys %v values %v", tree.Keys(), tree.Values())
		// a walk of the tree's own iterator, or of treemap's over a map holding the same entries,
		// or from IteratorAt a node of the tree
		var it rbtIter
		ref := &rbtRef{keys: keys, pos: -1}
		switch w := rng.Intn(3); w {
		case 0:
			ti := tree.Iterator()
			it = &ti
			tr.printf(" walk tree")
		case 1:
			m := treemap.NewWith(c.cmp)
			for _, k := range keys {
				m.Put(c.key(k), vals[k])
			}
			mi := m.Iterator()
			it = &mi
			tr.printf(" walk treemap")
		default:
			if len(keys) == 0 {
				ti := tree.Iterator()
				it = &ti
				tr.printf(" walk tree")
				break
			}
			i := rng.Intn(len(keys))
			ti := tree.IteratorAt(tree.GetNode(c.key(keys[i])))
			it = &ti
			ref.pos = i
			tr.printf(" walk at %d", keys[i])
		}
		walk := rng.Intn(60)
		for j := 0; j < walk; j++ {
			tr.printf("  %s", rbtStep(t, rng, c, it, ref, vals))
			steps++
		}
		// a walk while the tree changes under the iterator (outside the reference: transcript
		// only; a step may panic)
		if rng.Intn(4) == 0 {
			mutated++
			ti := tree.Iterator()
			for j := 0; j < 30; j++ {
				if rng.Intn(4) == 0 {
					k := rng.Intn(keyRange*2+1) - keyRange
					if rng.Intn(2) == 0 {
						tree.Remove(c.key(k))
						tr.printf("  mut -%d", k)
					} else {
						tree.Put(c.key(k), j)
						tr.printf("  mut +%d", k)
					}
				}
				var line string
				o := outcome(func() { line = rbtStep(t, rng, c, &ti, nil, nil) })
				tr.printf("  %s %s", line, o)
				steps++
				if o != "ok" {
					break
				}
			}
		}
	}
	// zero and nil-tree iterators: Next/Prev on an iterator whose tree is nil panics as gods'
	for _, f := range []func(*rbt.Iterator) bool{(*rbt.Iterator).Next, (*rbt.Iterator).Prev} {
		var zero rbt.Iterator
		tr.printf("zero iterator: %s", outcome(func() { f(&zero) }))
		e := rbt.NewWith(utils.IntComparator).Iterator()
		tr.printf("empty tree: %s", outcome(func() { tr.printf("  = %v", f(&e)) }))
		tr.printf("again: %s", outcome(func() { tr.printf("  = %v", f(&e)) }))
	}
	tr.printf("trees %d puts %d removes %d steps %d mutated walks %d", trees, puts, removes, steps, mutated)
	t.Logf("rbt iterator: %d trees, %d puts, %d removes, %d steps, %d walks under changes", trees, puts, removes, steps, mutated)
	tr.save(t)
}
