package dist

import (
	"os"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
)

// sequential is the history of the operations in order, each returning before the next is called.
func sequential(ins []k8s.Input, outs []k8s.Output) []porcupine.Operation {
	var ops []porcupine.Operation
	for i := range ins {
		ops = append(ops, porcupine.Operation{ClientId: ins[i].Client, Input: ins[i], Output: outs[i],
			Call: int64(2 * i), Return: int64(2*i + 1)})
	}
	return ops
}

// sharedCheck is RunStore's verdict on ops (CheckShared).
func sharedCheck(s k8s.Seeded, ops []porcupine.Operation) porcupine.CheckResult {
	r, _ := CheckShared(s, k8s.HistoryRevs(ops), ops, 0)
	return r
}

// TestSharedModel checks SharedModel (the driver's Model with foreign revisions) on small
// histories: it accepts what Model accepts, a history whose revisions skip the ones other clients
// wrote, the past reads of a store's revisions in such a gap, and a failed write that took effect
// after one; it rejects what is wrong but for the revision numbers.
func TestSharedModel(t *testing.T) {
	s := k8s.SeededAt(2, 3)
	seed1 := k8s.Obj{Namespace: "ns-1", Name: "pod-1", Value: "x", ResourceVersion: 2}
	seed2 := k8s.Obj{Namespace: "ns-2", Name: "pod-2", Value: "x", ResourceVersion: 3}
	create := k8s.Input{Kind: k8s.KCreate, Key: "ns-1/pod-11", Val: "y", UID: "u1"}
	created := func(rv uint64) k8s.Output {
		return k8s.Output{Namespace: "ns-1", Name: "pod-11", UID: "u1", Value: "y", RV: rv}
	}
	get := k8s.Input{Kind: k8s.KGet, Key: "ns-1/pod-11", Client: 1}
	past := func(rv uint64) k8s.Input {
		return k8s.Input{Kind: k8s.KList, ListKey: "/objs/", Recursive: true, MinRV: k8s.RVBytes(rv),
			Match: k8s.MExact, Client: 1}
	}
	listed := func(rv uint64, items ...k8s.Obj) k8s.Output {
		return k8s.Output{Items: k8s.EncodeItems(items), ListRV: rv}
	}
	cases := []struct {
		name string
		ins  []k8s.Input
		outs []k8s.Output
		ok   bool
		// Model's verdict too (only a history without foreign revisions)
		model bool
	}{
		{"no foreign revision", []k8s.Input{create, get}, []k8s.Output{created(4), created(4)}, true, true},
		{"foreign revisions before a write", []k8s.Input{create, get}, []k8s.Output{created(10), created(10)}, true, false},
		{"a wrong value", []k8s.Input{create, get},
			[]k8s.Output{created(10), {Namespace: "ns-1", Name: "pod-11", UID: "u1", Value: "z", RV: 10}}, false, false},
		{"a past read in the gap", []k8s.Input{create, past(7)},
			[]k8s.Output{created(10), listed(7, seed1, seed2)}, true, false},
		{"a past read in the gap sees the later write", []k8s.Input{create, past(7)},
			[]k8s.Output{created(10), listed(7, seed1, created10Obj(), seed2)}, false, false},
		{"a past read at the write", []k8s.Input{create, past(10)},
			[]k8s.Output{created(10), listed(10, seed1, created10Obj(), seed2)}, true, false},
		{"a not-found names the current revision", []k8s.Input{create, {Kind: k8s.KGet, Key: "ns-2/pod-22"}},
			[]k8s.Output{created(10), {Err: k8s.ENotFound, ErrKey: "/registry/objs/ns-2/pod-22", ErrRV: 15}}, true, false},
		{"a not-found below the last write", []k8s.Input{create, {Kind: k8s.KGet, Key: "ns-2/pod-22"}},
			[]k8s.Output{created(10), {Err: k8s.ENotFound, ErrKey: "/registry/objs/ns-2/pod-22", ErrRV: 9}}, false, false},
		{"a failed write that took effect after foreign revisions", []k8s.Input{create, get},
			[]k8s.Output{{Err: k8s.EOther}, created(20)}, true, false},
		{"a failed write seen, then a past read in the gap before it",
			[]k8s.Input{create, {Kind: k8s.KCreate, Key: "ns-1/pod-11", UID: "u2", Client: 2}, past(15), get},
			[]k8s.Output{{Err: k8s.EOther}, {Err: k8s.EExists, ErrKey: "/registry/objs/ns-1/pod-11"},
				listed(15, seed1, seed2), created(20)}, true, false},
		{"a failed read (compacted) tells nothing", []k8s.Input{create, past(7)},
			[]k8s.Output{created(10), {Err: k8s.EOther}}, true, false},
		{"a revision going back", []k8s.Input{create, {Kind: k8s.KCreate, Key: "ns-2/pod-22", UID: "u3"}},
			[]k8s.Output{created(10), {Namespace: "ns-2", Name: "pod-22", UID: "u3", RV: 9}}, false, false},
	}
	for _, c := range cases {
		ops := sequential(c.ins, c.outs)
		if r := sharedCheck(s, ops); (r == porcupine.Ok) != c.ok {
			t.Errorf("%s: SharedModel %v, want ok %v", c.name, r, c.ok)
		}
		if r := porcupine.CheckOperationsTimeout(s.Model(), ops, 0); (r == porcupine.Ok) != c.model {
			t.Errorf("%s: Model %v, want ok %v", c.name, r, c.model)
		}
		if c.ok && c.model != s.NoForeign(ops) {
			t.Errorf("%s: NoForeign %v", c.name, !c.model)
		}
	}
}

// TestSharedWatchList checks SharedModel on a watch-list (SendInitialEvents true) at a resource
// version above every revision the history writes, whose answer ends before its
// initial-events-end bookmark: Model's check accepts it only at a configuration at that resource
// version or above, so target moves there (G7; notes/k8s-dist-k4.md, "The gap"). The history
// linearizes (foreign revisions 4..10, then the watch: the store at 10 has pod-1 at 2), and every
// mode accepts it; with pod-1's value wrong, every mode rejects it.
func TestSharedWatchList(t *testing.T) {
	s := k8s.SeededAt(2, 3)
	in := k8s.Input{Kind: k8s.KWatch, WKey: "/objs/", Recursive: true, MinRV: k8s.RVBytes(10), SendInit: 2,
		Bookmarks: true, Match: k8s.MNotOlderThan}
	for _, c := range []struct {
		value string
		ok    bool
	}{{"x", true}, {"z", false}} {
		out := k8s.Output{WEvents: k8s.EncodeWEvents([]k8s.WEvent{{Type: k8s.WAdded,
			Obj: k8s.Obj{Namespace: "ns-1", Name: "pod-1", Value: c.value, ResourceVersion: 2}}})}
		ops := sequential([]k8s.Input{in}, []k8s.Output{out})
		for _, mode := range []int{k8s.Lazy, k8s.Eager, k8s.Full} {
			r := porcupine.CheckOperationsTimeout(s.SharedModel(k8s.HistoryRevs(ops), mode), ops, 0)
			if (r == porcupine.Ok) != c.ok {
				t.Errorf("value %q, mode %d: %v, want ok %v", c.value, mode, r, c.ok)
			}
		}
	}
}

// TestSharedGaps checks SharedModel on the three histories outside the driver's generator that
// linearize in the semantic model and that the search refused before G8, G9 and G10
// (notes/k8s-dist-k4.md, "K4-3"): each is accepted from its first accepting mode on (and by
// CheckShared), and rejected in every mode with a wrong value.
// G8: a create with an unparsable MinRV (a write never reads it) answering a revision above the
// seeds. G9: a pending create of a key without a name ("ns/"), a create at 10, then a Get of the
// first key showing it at 7 (an anchor although its answer has no name); Lazy, by design, writes
// the second create at 10 without landing the first, which it then cannot land at 7. G10: a Get-like kind
// (Kind 7, which mstep answers with mget) at a MinRV of 10, answering the seed at 2.
func TestSharedGaps(t *testing.T) {
	s := k8s.SeededAt(2, 3)
	cases := []struct {
		name string
		ins  []k8s.Input
		outs func(value string) []k8s.Output
		good string
		from int
	}{
		{"G8", []k8s.Input{{Kind: k8s.KCreate, Key: "ns-1/pod-11", Val: "y", UID: "u1", MinRV: "a"}},
			func(v string) []k8s.Output {
				return []k8s.Output{{Namespace: "ns-1", Name: "pod-11", UID: "u1", Value: v, RV: 10}}
			}, "y", k8s.Lazy},
		{"G9", []k8s.Input{{Kind: k8s.KCreate, Key: "ns/", Val: "y", UID: "u0"},
			{Kind: k8s.KCreate, Key: "ns/b", Val: "y", UID: "u2", Client: 1},
			{Kind: k8s.KGet, Key: "ns/", Client: 2}},
			func(v string) []k8s.Output {
				return []k8s.Output{{Err: k8s.EOther}, {Namespace: "ns", Name: "b", UID: "u2", Value: "y", RV: 10},
					{Namespace: "ns", UID: "u0", Value: v, RV: 7}}
			}, "y", k8s.Eager},
		{"G10", []k8s.Input{{Kind: 7, Key: "ns-1/pod-1", MinRV: k8s.RVBytes(10)}},
			func(v string) []k8s.Output {
				return []k8s.Output{{Namespace: "ns-1", Name: "pod-1", Value: v, RV: 2}}
			}, "x", k8s.Lazy},
	}
	for _, c := range cases {
		for _, value := range []string{c.good, "z"} {
			ok := value == c.good
			ops := sequential(c.ins, c.outs(value))
			for _, mode := range []int{k8s.Lazy, k8s.Eager, k8s.Full} {
				r := porcupine.CheckOperationsTimeout(s.SharedModel(k8s.HistoryRevs(ops), mode), ops, 0)
				if want := ok && mode >= c.from; (r == porcupine.Ok) != want {
					t.Errorf("%s, value %q, mode %d: %v, want ok %v", c.name, value, mode, r, want)
				}
			}
			if r := sharedCheck(s, ops); (r == porcupine.Ok) != ok {
				t.Errorf("%s, value %q: CheckShared %v, want ok %v", c.name, value, r, ok)
			}
		}
	}
}

func created10Obj() k8s.Obj {
	return k8s.Obj{Namespace: "ns-1", Name: "pod-11", UID: "u1", Value: "y", ResourceVersion: 10}
}

// TestReplayHistory checks a store history RunStore dumped (DIST_DUMP; the file named by
// DIST_HISTORY) as RunStore does, for profiling the check; with DIST_CROSS set, every watch step
// is checked both by watchOk and by the shared model's indexed copy of it, which must agree;
// DIST_CHECK_TIMEOUT (a duration) replaces each mode's CheckTimeout.
func TestReplayHistory(t *testing.T) {
	p := os.Getenv("DIST_HISTORY")
	if p == "" {
		t.Skip("set DIST_HISTORY to a dumped history")
	}
	seeded, ops, err := LoadHistory(p)
	if err != nil {
		t.Fatal(err)
	}
	k8s.CrossCheckWatches(os.Getenv("DIST_CROSS") != "")
	defer k8s.CrossCheckWatches(false)
	start := time.Now()
	revs := k8s.HistoryRevs(ops)
	timeout := CheckTimeout
	if d, err := time.ParseDuration(os.Getenv("DIST_CHECK_TIMEOUT")); err == nil {
		timeout = d
	}
	r, mode := CheckShared(seeded, revs, ops, timeout)
	t.Logf("%d operations: %v (mode %d) in %v", len(ops), r, mode, time.Since(start))
	// the same history with one Get's answer wrong (another value) is rejected in every mode
	for i, op := range ops {
		out := op.Output.(k8s.Output)
		if op.Input.(k8s.Input).Kind != k8s.KGet || out.Err != k8s.ENone || out.Name == "" {
			continue
		}
		bad := append([]porcupine.Operation{}, ops...)
		out.Value += "!"
		bad[i].Output = out
		for _, mode := range []int{k8s.Lazy, k8s.Eager, k8s.Full} {
			start := time.Now()
			r := porcupine.CheckOperationsTimeout(seeded.SharedModel(k8s.HistoryRevs(bad), mode), bad, CheckTimeout)
			t.Logf("a wrong Get (operation %d), mode %d: %v in %v", i, mode, r, time.Since(start))
			if r != porcupine.Illegal {
				t.Errorf("a wrong Get passed: %v", r)
			}
		}
		break
	}
}
