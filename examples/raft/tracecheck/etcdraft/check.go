package etcdraft

import (
	"encoding/json"
	"fmt"
	"hash/fnv"
	"time"

	"github.com/anishathalye/porcupine"
)

// Result is the outcome of checking a trace.
type Result struct {
	// OK: some behavior of the trace specification steps through every line (TLC's
	// TraceMatched), and no state reached violates an invariant.
	OK bool
	// Line is the first line no state could step through (when !OK and Violation == "").
	Line int
	// Violation is the first invariant a reached state violated, and Bad the state.
	Violation string
	ViolLine  int
	Bad       *State
	// MaxStates is the largest number of distinct states at a line.
	MaxStates int
	// Before are the states at Line (when the trace is not matched): none of them steps
	// through it.
	Before []TState
}

func (r Result) String() string {
	switch {
	case r.OK:
		return fmt.Sprintf("ok (at most %d states per line)", r.MaxStates)
	case r.Violation != "":
		return fmt.Sprintf("invariant %s violated at line %d", r.Violation, r.ViolLine)
	}
	return fmt.Sprintf("trace not matched: no behavior steps through line %d", r.Line)
}

// CheckTrace checks t as TLC does (Traceetcdraft.cfg): a breadth-first search, line by line, of
// the states TraceNext reaches, deduplicated by TLC's view <<vars, l>>, checking every state
// against Invariants (when invariants is set). The trace is matched when some state reaches past
// its last line.
func CheckTrace(t *Trace, invariants bool) Result {
	var r Result
	frontier := []TState{t.Init()}
	if invariants {
		if v := frontier[0].S.Violated(); v != "" {
			return Result{Violation: v, ViolLine: 0, Bad: frontier[0].S}
		}
	}
	for l := 1; l <= t.Len(); l++ {
		var next []TState
		seen := map[string]bool{}
		for _, ts := range frontier {
			for _, s2 := range t.StepLine(ts) {
				k := s2.Key()
				if seen[k] {
					continue
				}
				seen[k] = true
				if invariants {
					if v := s2.S.Violated(); v != "" {
						return Result{Violation: v, ViolLine: l, Bad: s2.S}
					}
				}
				next = append(next, s2)
			}
		}
		if len(next) == 0 {
			r.Line = l
			r.Before = frontier
			return r
		}
		r.MaxStates = max(r.MaxStates, len(next))
		frontier = next
	}
	r.OK = true
	return r
}

// pstate is a porcupine state of Model: a trace-specification state with its key cached.
type pstate struct {
	ts  TState
	key string
}

// Explain describes why no state of r.Before steps through r.Line: the line, and for each state
// the variables of the line's node and, for a received message's line, the messages in transit to
// it.
func Explain(t *Trace, r Result) string {
	if r.OK || r.Line == 0 {
		return ""
	}
	ev := t.Event(r.Line)
	b, _ := json.Marshal(ev)
	out := fmt.Sprintf("line %d: %s\n", r.Line, b)
	for k, ts := range r.Before {
		out += fmt.Sprintf("state %d of %d (pl %d):\n%s", k+1, len(r.Before), ts.PL, ts.S)
		if ev.Msg != nil {
			for _, m := range ts.S.Messages.Domain() {
				if fmt.Sprint(m.Dest) == ev.Msg.To {
					out += fmt.Sprintf("  in transit: %v x%d\n", m, ts.S.Messages.Count(m))
				}
			}
		}
	}
	return out
}

func newPState(ts TState) *pstate { return &pstate{ts: ts, key: ts.Key()} }

// Model is the trace specification of t as a porcupine NondeterministicModel: an operation is a
// line of the trace (its input the line number l, its output unused), and a state of the model is
// a state of the trace specification at that line; Step is StepLine (every state at line l+1),
// keeping only the states that satisfy Invariants when invariants is set.
func Model(t *Trace, invariants bool) porcupine.NondeterministicModel {
	return porcupine.NondeterministicModel{
		Init: func() []interface{} {
			return []interface{}{newPState(t.Init())}
		},
		Step: func(state, input, output interface{}) []interface{} {
			ps := state.(*pstate)
			l := input.(int)
			if ps.ts.L != l {
				return nil
			}
			var out []interface{}
			for _, s2 := range t.StepLine(ps.ts) {
				if invariants && s2.S.Violated() != "" {
					continue
				}
				out = append(out, newPState(s2))
			}
			return out
		},
		Equal: func(a, b interface{}) bool { return a.(*pstate).key == b.(*pstate).key },
		Hash: func(state interface{}) uint64 {
			h := fnv.New64a()
			h.Write([]byte(state.(*pstate).key))
			return h.Sum64()
		},
		DescribeOperation: func(input, output interface{}) string {
			l := input.(int)
			ev := t.Event(l)
			return fmt.Sprintf("%d: %s %s", l, ev.Name, ev.NID)
		},
		DescribeState: func(state interface{}) string { return state.(*pstate).ts.S.String() },
	}
}

// History is t as a porcupine history: line l is the operation with input l, called at 2l and
// returning at 2l+1 (so the lines are totally ordered: porcupine's only linearization is the
// trace's order).
func History(t *Trace) []porcupine.Operation {
	ops := make([]porcupine.Operation, t.Len())
	for l := 1; l <= t.Len(); l++ {
		ops[l-1] = porcupine.Operation{ClientId: 0, Input: l, Output: nil, Call: int64(2 * l), Return: int64(2*l + 1)}
	}
	return ops
}

// CheckPorcupine checks t with porcupine (CheckOperationsTimeout of Model's ToModel on History).
func CheckPorcupine(t *Trace, invariants bool, timeout time.Duration) porcupine.CheckResult {
	m := Model(t, invariants)
	return porcupine.CheckOperationsTimeout(m.ToModel(), History(t), timeout)
}
