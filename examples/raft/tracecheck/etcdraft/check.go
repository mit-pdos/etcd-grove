package etcdraft

import (
	"fmt"
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
	// EvalError is where TLC would stop with an error (Eval's What), at line ErrLine; Eval has its
	// numbers.
	EvalError string
	Eval      EvalError
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
		return fmt.Sprintf("evaluation error at line %d: %v", r.ErrLine, r.Eval)
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
			r = Result{EvalError: e.What, Eval: e, ErrLine: l, Branched: r.Branched}
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
		for _, ts := range frontier {
			succ, info := t.StepLine(ts, invariants)
			if info.Branched && r.Branched == 0 {
				r.Branched = l
			}
			if info.Violation != "" {
				return Result{Violation: info.Violation, ViolLine: l, Bad: info.Bad, Branched: r.Branched}
			}
			for _, s2 := range succ {
				if indexOf(next, s2) < 0 {
					next = append(next, s2)
				}
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
