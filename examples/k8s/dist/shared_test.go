package dist

import (
	"os"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"

	k8s "github.com/mit-pdos/etcd-grove/examples/k8s/dist/storecopy"
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

// sharedCheck is RunStore's verdict on ops: the fast SharedModel, then the full one on Illegal.
func sharedCheck(s k8s.Seeded, ops []porcupine.Operation) porcupine.CheckResult {
	revs := k8s.HistoryRevs(ops)
	r := porcupine.CheckOperationsTimeout(s.SharedModel(revs, false), ops, 0)
	if r == porcupine.Illegal {
		r = porcupine.CheckOperationsTimeout(s.SharedModel(revs, true), ops, 0)
	}
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

func created10Obj() k8s.Obj {
	return k8s.Obj{Namespace: "ns-1", Name: "pod-11", UID: "u1", Value: "y", ResourceVersion: 10}
}

// TestReplayHistory checks a store history RunStore dumped (DIST_DUMP; the file named by
// DIST_HISTORY) as RunStore does, for profiling the check.
func TestReplayHistory(t *testing.T) {
	p := os.Getenv("DIST_HISTORY")
	if p == "" {
		t.Skip("set DIST_HISTORY to a dumped history")
	}
	seeded, ops, err := LoadHistory(p)
	if err != nil {
		t.Fatal(err)
	}
	start := time.Now()
	revs := k8s.HistoryRevs(ops)
	r := porcupine.CheckOperationsTimeout(seeded.SharedModel(revs, false), ops, CheckTimeout)
	t.Logf("%d operations: %v in %v", len(ops), r, time.Since(start))
	// the same history with one Get's answer wrong (another value) is rejected, by the fast model
	// and by the full one
	for i, op := range ops {
		out := op.Output.(k8s.Output)
		if op.Input.(k8s.Input).Kind != k8s.KGet || out.Err != k8s.ENone || out.Name == "" {
			continue
		}
		bad := append([]porcupine.Operation{}, ops...)
		out.Value += "!"
		bad[i].Output = out
		for _, full := range []bool{false, true} {
			start := time.Now()
			r := porcupine.CheckOperationsTimeout(seeded.SharedModel(k8s.HistoryRevs(bad), full), bad, CheckTimeout)
			t.Logf("a wrong Get (operation %d), full %v: %v in %v", i, full, r, time.Since(start))
			if r != porcupine.Illegal {
				t.Errorf("a wrong Get passed: %v", r)
			}
		}
		break
	}
}
