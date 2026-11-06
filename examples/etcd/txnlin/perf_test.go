package txnlin

// The performance measurement of the model's canonical form (notes/txnlin-perf-plan.md, "Go first"):
// oldModel is the model before it (pending writes in arrival order, a state an unordered list
// deduplicated by a linear scan, no Hash), kept here to compare with Model on a saved history
// (TestPerfHistory) and on random ones (TestOldNewDifferential).

import (
	"encoding/gob"
	"math/rand"
	"os"
	"sort"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
)

// oldCfg and oldState are mcfg and state before the canonical form.
type oldCfg struct {
	st   store
	pend []Input
}

type oldState []oldCfg

func oldConfigEqual(a, b oldCfg) bool {
	if !storeEqual(a.st, b.st) || len(a.pend) != len(b.pend) {
		return false
	}
	for i := range a.pend {
		if !inputEqual(a.pend[i], b.pend[i]) {
			return false
		}
	}
	return true
}

func oldAddConfig(s oldState, c oldCfg) oldState {
	for _, d := range s {
		if oldConfigEqual(c, d) {
			return s
		}
	}
	return append(s, c)
}

// oldRemoveAt returns pend without its i-th input (a new slice).
func oldRemoveAt(pend []Input, i int) []Input {
	out := make([]Input, 0, len(pend))
	out = append(out, pend[:i]...)
	return append(out, pend[i+1:]...)
}

// oldClosure adds to s every configuration reachable by pending writes taking effect.
func oldClosure(s oldState) oldState {
	out := oldState{}
	work := append([]oldCfg{}, s...)
	for len(work) > 0 {
		c := work[len(work)-1]
		work = work[:len(work)-1]
		n := len(out)
		out = oldAddConfig(out, c)
		if len(out) == n {
			continue
		}
		for i, w := range c.pend {
			st, _ := mstep(w, c.st)
			work = append(work, oldCfg{st: st, pend: oldRemoveAt(c.pend, i)})
		}
	}
	return out
}

// oldStep returns the configurations c steps to by (in, out): a call that returned no error took
// effect and answered the model's output; a failed write becomes pending; a failed read does
// nothing.
func oldStep(c oldCfg, in Input, out Output) []oldCfg {
	if out.Err {
		if isWrite(in) {
			pend := make([]Input, 0, len(c.pend)+1)
			pend = append(pend, in)
			pend = append(pend, c.pend...)
			return []oldCfg{{st: c.st, pend: pend}}
		}
		return []oldCfg{c}
	}
	st, o := mstep(in, c.st)
	if !outEqual(in.Kind, out, o) {
		return nil
	}
	return []oldCfg{{st: st, pend: c.pend}}
}

// oldModel is etcd's KV as a porcupine model: the store starts empty at revision 1; a call that
// returned no error took effect at once and answered as the model; a failed write may take
// effect at any later time, or never; a failed read constrains nothing.
func oldModel() porcupine.Model {
	return porcupine.Model{
		Init: func() any { return oldState{oldCfg{st: store{rev: 1}}} },
		Step: func(st, input, output any) (bool, any) {
			in := input.(Input)
			out := output.(Output)
			next := oldState{}
			for _, c := range st.(oldState) {
				for _, d := range oldStep(c, in, out) {
					next = oldAddConfig(next, d)
				}
			}
			next = oldClosure(next)
			return len(next) > 0, next
		},
		Equal: func(a, b any) bool {
			sa := a.(oldState)
			sb := b.(oldState)
			if len(sa) != len(sb) {
				return false
			}
			for i := range sa {
				if !oldConfigEqual(sa[i], sb[i]) {
					return false
				}
			}
			return true
		},
	}
}

// perfStats are a check's counts: Step calls, the largest state, the most pending writes of a
// configuration.
type perfStats struct {
	steps     int
	peakState int
	peakK     int
}

// instrument wraps m's Step to count into ps; size gives a state's size and most pending writes.
func instrument(m porcupine.Model, ps *perfStats, size func(any) (int, int)) porcupine.Model {
	inner := m.Step
	m.Step = func(st, in, out any) (bool, any) {
		ok, next := inner(st, in, out)
		ps.steps++
		n, k := size(next)
		if n > ps.peakState {
			ps.peakState = n
		}
		if k > ps.peakK {
			ps.peakK = k
		}
		return ok, next
	}
	return m
}

func newSize(s any) (int, int) {
	k := 0
	for _, c := range s.(state) {
		if len(c.pend) > k {
			k = len(c.pend)
		}
	}
	return len(s.(state)), k
}

func oldSize(s any) (int, int) {
	k := 0
	for _, c := range s.(oldState) {
		if len(c.pend) > k {
			k = len(c.pend)
		}
	}
	return len(s.(oldState)), k
}

func init() {
	gob.Register(Input{})
	gob.Register(Output{})
}

// TestPerfHistory checks the history in $TXNLIN_HIST (a gob of []porcupine.Operation, as
// lintest's LINTEST_DUMP diagnostic wrote /shared/tmp/t1-diag/hist3.gob) with Model and with
// oldModel (oldModel given $TXNLIN_OLD_TIMEOUT, default 20m; skipped if "0"), and reports each
// one's verdict, check time, Step calls per second, largest state and most pending writes.
func TestPerfHistory(t *testing.T) {
	path := os.Getenv("TXNLIN_HIST")
	if path == "" {
		t.Skip("TXNLIN_HIST not set")
	}
	f, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	var ops []porcupine.Operation
	err = gob.NewDecoder(f).Decode(&ops)
	f.Close()
	if err != nil {
		t.Fatal(err)
	}
	nErr, nErrW := 0, 0
	for _, op := range ops {
		if op.Output.(Output).Err {
			nErr++
			if isWrite(op.Input.(Input)) {
				nErrW++
			}
		}
	}
	t.Logf("%d operations, %d failed, %d failed writes", len(ops), nErr, nErrW)
	sort.SliceStable(ops, func(i, j int) bool { return ops[i].Call < ops[j].Call })

	run := func(name string, m porcupine.Model, size func(any) (int, int), timeout time.Duration) porcupine.CheckResult {
		var ps perfStats
		t0 := time.Now()
		r := porcupine.CheckOperationsTimeout(instrument(m, &ps, size), ops, timeout)
		d := time.Since(t0)
		t.Logf("%s: %v in %v; %d steps, %.0f steps/s, peak |state| %d, peak k %d",
			name, r, d.Round(time.Millisecond), ps.steps, float64(ps.steps)/d.Seconds(), ps.peakState, ps.peakK)
		return r
	}
	models := os.Getenv("TXNLIN_MODELS")
	rNew := porcupine.Unknown
	if models != "old" {
		rNew = run("new", Model(), newSize, 0)
	}
	if models == "new" {
		return
	}
	oldTimeout := 20 * time.Minute
	if s := os.Getenv("TXNLIN_OLD_TIMEOUT"); s != "" {
		d, err := time.ParseDuration(s)
		if err != nil {
			t.Fatal(err)
		}
		oldTimeout = d
	}
	if oldTimeout == 0 {
		return
	}
	rOld := run("old", oldModel(), oldSize, oldTimeout)
	if rOld != porcupine.Unknown && rNew != porcupine.Unknown && rOld != rNew {
		t.Fatalf("verdicts differ: new %v, old %v", rNew, rOld)
	}
}

// TestOldNewDifferential checks that Model and oldModel give the same verdict on random histories
// (robust_test.go's randomHistory: a sixth of the calls fail, half of the failed writes having
// taken effect; half the histories with one output corrupted), up to 24 operations.
func TestOldNewDifferential(t *testing.T) {
	rng := rand.New(rand.NewSource(2))
	legal, illegal, withW, maxW := 0, 0, 0, 0
	for iter := 0; iter < 5000; iter++ {
		ours, _ := randomHistory(rng, 3, 2+rng.Intn(23))
		w := 0
		for _, op := range ours {
			if op.Output.(Output).Err && isWrite(op.Input.(Input)) {
				w++
			}
		}
		if w > 0 {
			withW++
		}
		if w > maxW {
			maxW = w
		}
		a := porcupine.CheckOperations(Model(), ours)
		b := porcupine.CheckOperations(oldModel(), ours)
		if a != b {
			t.Fatalf("iteration %d: Model() %v, oldModel() %v on\n%+v", iter, a, b, ours)
		}
		if a {
			legal++
		} else {
			illegal++
		}
	}
	t.Logf("agreed on %d legal and %d illegal histories; %d with failed writes (at most %d)",
		legal, illegal, withW, maxW)
	if legal < 100 || illegal < 100 || withW < 1000 {
		t.Fatalf("too few: %d legal, %d illegal, %d with failed writes", legal, illegal, withW)
	}
}
