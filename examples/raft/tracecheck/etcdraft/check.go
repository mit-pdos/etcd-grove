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
	// OK: some behavior of the trace specification steps through every line, no state reached
	// violates an invariant (when checked), and no evaluation fails. That is the property
	// TraceMatched is meant to state ("at least one trace fully matches the log"); TLC's check of
	// it is stricter (TLCOK).
	OK bool
	// Branched is the first line at which some state had more than one new successor, 0 if none.
	// TLC's TraceMatched, `[](l <= Len(TraceLog) => [](TLCGet("queue") = 1 \/ l > Len(TraceLog)))`,
	// fails as soon as its breadth-first search's queue holds more than one state, so it rejects
	// a trace whose search branches anywhere, even where every branch, or one, matches.
	Branched int
	// Line is the first line no state could step through (when !OK and the failure is neither
	// a violation nor an evaluation error).
	Line int
	// Violation is the first invariant a reached state violated, ViolLine its line, Bad the state.
	Violation string
	ViolLine  int
	Bad       *State
	// EvalError is where TLC would stop with an error, at line ErrLine.
	EvalError string
	ErrLine   int
	// MaxStates is the largest number of distinct states at a line.
	MaxStates int
	// Before are the states at Line (when the trace is not matched): none of them steps
	// through it.
	Before []TState
}

// TLCOK is TLC's verdict: OK, and the search never branched.
func (r Result) TLCOK() bool { return r.OK && r.Branched == 0 }

func (r Result) String() string {
	switch {
	case r.OK && r.Branched != 0:
		return fmt.Sprintf("matched, but the search branches at line %d (TLC's TraceMatched would fail)", r.Branched)
	case r.OK:
		return fmt.Sprintf("ok (at most %d states per line)", r.MaxStates)
	case r.EvalError != "":
		return fmt.Sprintf("evaluation error at line %d: %s", r.ErrLine, r.EvalError)
	case r.Violation != "":
		return fmt.Sprintf("invariant %s violated at line %d", r.Violation, r.ViolLine)
	}
	return fmt.Sprintf("trace not matched: no behavior steps through line %d", r.Line)
}

// CheckTrace checks t as TLC does (Traceetcdraft.cfg): a breadth-first search, line by line, of
// the states TraceNext reaches, deduplicated by TLC's view <<vars, l>>, checking every state
// reached against Invariants (when invariants is set). The trace is matched when some state
// reaches past its last line; Result.Branched records where TLC's stricter TraceMatched would
// fail. An evaluation TLC would fail is reported as such (Result.EvalError).
func CheckTrace(t *Trace, invariants bool) (r Result) {
	l := 0
	defer func() {
		if x := recover(); x != nil {
			e, ok := x.(EvalError)
			if !ok {
				panic(x)
			}
			r = Result{EvalError: e.Msg, ErrLine: l, Branched: r.Branched}
		}
	}()
	frontier := []TState{t.Init()}
	if invariants {
		if v := frontier[0].S.Violated(); v != "" {
			return Result{Violation: v, ViolLine: 0, Bad: frontier[0].S}
		}
	}
	for l = 1; l <= t.Len(); l++ {
		var next []TState
		seen := map[string]bool{}
		for _, ts := range frontier {
			succ, info := t.StepLine(ts, invariants)
			if info.Branched && r.Branched == 0 {
				r.Branched = l
			}
			if info.Violation != "" {
				return Result{Violation: info.Violation, ViolLine: l, Bad: info.Bad, Branched: r.Branched}
			}
			for _, s2 := range succ {
				k := s2.Key()
				if seen[k] {
					continue
				}
				seen[k] = true
				next = append(next, s2)
			}
		}
		if len(next) == 0 {
			r.Line = l
			r.Before = frontier
			return r
		}
		if len(next) > 1 && r.Branched == 0 {
			r.Branched = l
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
// a state of the trace specification at that line; Step is StepLine (every state at line l+1). A
// line from a state where an invariant is violated (when invariants is set) or an evaluation fails
// has no successor. Porcupine's acceptance is "some path matches" (Result.OK), not TLC's stricter
// TraceMatched (Result.TLCOK); with a search that never branches they are the same.
func Model(t *Trace, invariants bool) porcupine.NondeterministicModel {
	return porcupine.NondeterministicModel{
		Init: func() []interface{} {
			return []interface{}{newPState(t.Init())}
		},
		Step: func(state, input, output interface{}) (out []interface{}) {
			// An evaluation TLC would fail, or an invariant violated by any state reached
			// (intermediate steps included), fails the line: porcupine then answers Illegal, as
			// TLC reports an error. (A state that violates no invariant is not filtered out: a
			// violation is a failure, not a dead end.)
			defer func() {
				if x := recover(); x != nil {
					if _, ok := x.(EvalError); !ok {
						panic(x)
					}
					out = nil
				}
			}()
			ps := state.(*pstate)
			l := input.(int)
			if ps.ts.L != l {
				return nil
			}
			succ, info := t.StepLine(ps.ts, invariants)
			if info.Violation != "" {
				return nil
			}
			for _, s2 := range succ {
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
