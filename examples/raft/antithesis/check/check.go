package check

// Kind is the kind of a verdict, as streamcheck.py prints it.
type Kind int

const (
	// Accepted: the stream ended and every event matched (ACCEPTED n).
	Accepted Kind = iota
	// Rejected: no successor takes event K (REJECTED k).
	Rejected
	// Violated: the state after event K breaks an invariant (VIOLATED k names).
	Violated
	// Error: TLC would stop with an evaluation error (ERROR); Check only, Run panics.
	Error
)

// Verdict is the outcome of checking a stream. K is n for Accepted (the number of events), the
// event's index (from 1) otherwise. Names: for Violated, the invariant TLC reports (the first of
// the configuration's INVARIANTS that fails: ElectionSafety, OneVotePerTerm, Safe), and for Safe
// the names in viol (as streamcheck.py prints them, sorted).
type Verdict struct {
	Kind  Kind
	K     int
	Names []string
	Err   string
}

// violated is the invariants of EtcdBinding*.cfg (ElectionSafety, OneVotePerTerm, Safe; B 782
// `Safe == viol = {}`) that s breaks, as TLC reports them: the first that fails, or nil.
func violated(s *State) []string {
	if !s.ElectionSafety() {
		return []string{"ElectionSafety"}
	}
	if !s.OneVotePerTerm() {
		return []string{"OneVotePerTerm"}
	}
	if len(s.Viol) != 0 {
		return s.Viol
	}
	return nil
}

// Checker follows a stream one event at a time, as TLC with TraceKit's StreamEvent: the state
// reached so far (B 776 `TraceSpec`, with GC steps taken whenever due), and the verdict once
// there is one.
type Checker struct {
	State *State
	// Done: a verdict was reached (Rejected or Violated); Verdict holds it.
	Done    bool
	Verdict Verdict
}

// NewChecker is the checker at Init0. (Init0 breaks no invariant.)
func NewChecker(cfg *Config) *Checker {
	return &Checker{State: Init0(cfg)}
}

// Next takes the next event (event State.I). It panics with an EvalError where TLC would stop
// with one. After a verdict it does nothing.
func (c *Checker) Next(ev *Event) {
	if c.Done {
		return
	}
	s := c.State
	// B 775 `Next0 == (GC \/ Step) /\ UNCHANGED read`: GC while due (Step requires ~GCDue).
	for s.GCDue() {
		s = s.GC()
		// A GC state forgets facts and breaks nothing the invariants test; checked as TLC does,
		// at the last event requested (s.I - 1).
		if v := violated(s); v != nil {
			c.State = s
			c.Done = true
			c.Verdict = Verdict{Kind: Violated, K: s.I - 1, Names: v}
			return
		}
	}
	ns, ok := s.Step(ev)
	if !ok {
		c.State = s
		c.Done = true
		c.Verdict = Verdict{Kind: Rejected, K: s.I}
		return
	}
	c.State = ns
	if v := violated(ns); v != nil {
		c.Done = true
		c.Verdict = Verdict{Kind: Violated, K: s.I, Names: v}
	}
}

// End is the verdict once the stream has ended (TraceKit's [e |-> "End"]): the one reached, or
// Accepted with the number of events taken.
func (c *Checker) End() Verdict {
	if c.Done {
		return c.Verdict
	}
	return Verdict{Kind: Accepted, K: c.State.I - 1}
}

// Run checks a whole stream. It panics with an EvalError where TLC would stop with an error.
func Run(cfg *Config, evs []*Event) Verdict {
	c := NewChecker(cfg)
	for _, ev := range evs {
		c.Next(ev)
		if c.Done {
			break
		}
	}
	return c.End()
}
