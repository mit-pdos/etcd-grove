// Package check is a transcription into Go of Antithesis's TLA+ model of etcd-io/raft
// (`antithesis-fm/spec/EtcdRaft.tla`) and of its trace binding (`antithesis-fm/spec/EtcdBinding.tla`,
// with the operators of `antithesis-fm/tracekit/tla/TraceKit.tla` it uses), vendored under
// third_party/etcd-raft-formalized/ at the commit its README names. It checks a stream of reports
// (rawnode's, `antithesis-fm/rawnode/node.go`) as `antithesis-fm/tracekit/check/streamcheck.py`
// checks it with TLC: Check returns ACCEPTED n, REJECTED k, VIOLATED k (with the properties
// broken) or ERROR (where TLC would stop with an evaluation error).
//
// The binding is deterministic: from a state, at most one of GC and Step is enabled, and each
// determines its successor (every primed variable is given by an equality; its CHOOSEs pick a
// least element). So TLC's breadth-first search with one worker keeps one state per event, and so
// does Check: no search (notes/antithesis-check-design.md, "Nondeterminism").
//
// The transcription follows the TLA+ text definition by definition, with the same names; each
// function's comment names the definition and its lines in the vendored files (R = EtcdRaft.tla,
// B = EtcdBinding.tla). Conjunctions are evaluated in the TLA+ order, and a LET definition only
// where the TLA+ uses it, so that the evaluation errors TLC would raise are raised at the same
// points (as panics with an EvalError, which Check reports as ERROR).
//
// TLA+ values become Go values:
//
//   - a server is its name, a string (Nil is "");
//   - a set of servers is a Set, a sorted slice of names without duplicates;
//   - a sequence is a slice (TLA+'s s[k] is s[k-1]); a log is a []Entry;
//   - a record is a struct; a function on Server is a slice indexed like Config.Server;
//   - a function on terms (ledLog, ledConf, ledAt, elAt, termLen) is a slice of (term, value)
//     pairs sorted by term, its DOMAIN the terms present;
//   - the facts of msgs (vote requests, grants, acks: the binding never keeps a request to append)
//     are Facts, one struct with every field of the three shapes, a field its shape lacks zero.
//
// Values are never written once built: an action builds its successor from copies (the set*
// helpers).
//
// The model's commits, applied and read are left out: the binding never changes them (it checks
// its safety properties on chain and termLen instead, B 50-52) and nothing it evaluates reads them.
//
// Go subset (for Goose, as examples/raft/tracecheck/etcdraft): slices, structs, strings compared
// whole, integer arithmetic, panics; no maps, closures, generics, fmt, sort or strings in the
// checking code (fmt only in String methods).
package check

// EvalError is an evaluation error TLC would raise (a sequence applied outside its domain, a field
// a record lacks, values of different kinds compared): the transcription panics with one, and
// Check reports it as ERROR.
type EvalError struct {
	What string
}

func (e EvalError) Error() string { return "TLC evaluation error: " + e.What }

func evalError(what string) {
	panic(EvalError{What: what})
}

// ---------------------------------------------------------------------------------------------
// Sets of servers.

// Set is a finite set of server names: sorted, without duplicates. Never written.
type Set []string

func strLess(a, b string) bool { return a < b }

// SetAdd is `s \cup {x}`.
func SetAdd(s Set, x string) Set {
	k := 0
	for k < len(s) && strLess(s[k], x) {
		k++
	}
	if k < len(s) && s[k] == x {
		return s
	}
	out := make(Set, 0, len(s)+1)
	out = append(out, s[:k]...)
	out = append(out, x)
	out = append(out, s[k:]...)
	return out
}

// SetOf is the set of the elements of a sequence: R 138 `Range(s)`.
func SetOf(xs []string) Set {
	var s Set
	for _, x := range xs {
		s = SetAdd(s, x)
	}
	return s
}

// Has is `x \in s`.
func (s Set) Has(x string) bool {
	for _, y := range s {
		if y == x {
			return true
		}
	}
	return false
}

// Union is `s \cup t`.
func (s Set) Union(t Set) Set {
	out := s
	for _, x := range t {
		out = SetAdd(out, x)
	}
	return out
}

// Minus is `s \ t`.
func (s Set) Minus(t Set) Set {
	var out Set
	for _, x := range s {
		if !t.Has(x) {
			out = append(out, x)
		}
	}
	return out
}

// Equal is `s = t`.
func (s Set) Equal(t Set) bool {
	if len(s) != len(t) {
		return false
	}
	for k := range s {
		if s[k] != t[k] {
			return false
		}
	}
	return true
}

// interCount is `Cardinality(s \cap t)`.
func interCount(s, t Set) int {
	n := 0
	for _, x := range s {
		if t.Has(x) {
			n++
		}
	}
	return n
}

// stringsEqual is equality of two sequences of strings.
func stringsEqual(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if a[k] != b[k] {
			return false
		}
	}
	return true
}

// ---------------------------------------------------------------------------------------------
// Entries and logs.

// Value is an entry's value: a string (a command's payload, "" for the others), or for a "conf"
// entry the record [add, remove, joint, leave] (R 136-137), add and remove sequences of names.
type Value struct {
	IsRec  bool
	Str    string
	Add    []string
	Remove []string
	Joint  bool
	Leave  bool
}

// Equal is `v = w`. TLC cannot compare a string with a record: an EvalError.
func (v Value) Equal(w Value) bool {
	if v.IsRec != w.IsRec {
		evalError("a string compared with a record (an entry's value)")
	}
	if !v.IsRec {
		return v.Str == w.Str
	}
	return stringsEqual(v.Add, w.Add) && stringsEqual(v.Remove, w.Remove) && v.Joint == w.Joint &&
		v.Leave == w.Leave
}

// rec is v as a record (its fields are read): an EvalError for a string.
func (v Value) rec() Value {
	if !v.IsRec {
		evalError("a field of a string (an entry's value read as a change)")
	}
	return v
}

// Entry is a log entry, `[term |-> t, type |-> ty, value |-> v]` (R 133 `Entry`).
type Entry struct {
	Term  int
	Type  string
	Value Value
}

// Equal is `e = f`.
func (e Entry) Equal(f Entry) bool {
	if e.Term != f.Term || e.Type != f.Type {
		return false
	}
	return e.Value.Equal(f.Value)
}

// EntriesEqual is equality of two sequences of entries.
func EntriesEqual(a, b []Entry) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if !a[k].Equal(b[k]) {
			return false
		}
	}
	return true
}

// At is `l[k]`: an EvalError outside 1..Len(l).
func At(l []Entry, k int) Entry {
	if k < 1 || k > len(l) {
		evalError("a sequence of entries applied outside its domain")
	}
	return l[k-1]
}

// SubSeq is Sequences' `SubSeq(s, m, n)`: <<>> when m > n, otherwise s[m..n], an EvalError if
// that is not within 1..Len(s) (as TLC's SubSeq).
func SubSeq(s []Entry, m, n int) []Entry {
	if m > n {
		return nil
	}
	if m < 1 || n > len(s) {
		evalError("SubSeq outside the sequence")
	}
	return s[m-1 : n]
}

// Concat is `a \o b`, a new slice.
func Concat(a, b []Entry) []Entry {
	out := make([]Entry, 0, len(a)+len(b))
	out = append(out, a...)
	out = append(out, b...)
	return out
}

// IsPrefix is R 130 `IsPrefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))`.
func IsPrefix(a, b []Entry) bool {
	return len(a) <= len(b) && EntriesEqual(a, SubSeq(b, 1, len(a)))
}

// TermAt is R 131 `TermAt(l, k) == IF k > 0 /\ k <= Len(l) THEN l[k].term ELSE 0`.
func TermAt(l []Entry, k int) int {
	if k > 0 && k <= len(l) {
		return l[k-1].Term
	}
	return 0
}

// Min is R 125.
func Min(a, b int) int {
	if a <= b {
		return a
	}
	return b
}

// Max is R 126.
func Max(a, b int) int {
	if a >= b {
		return a
	}
	return b
}

// ---------------------------------------------------------------------------------------------
// Configurations.

// Conf is a configuration `[in |-> ..., out |-> ...]` (R 95-96).
type Conf struct {
	In  Set
	Out Set
}

// Equal is `C = D`.
func (c Conf) Equal(d Conf) bool { return c.In.Equal(d.In) && c.Out.Equal(d.Out) }

// ---------------------------------------------------------------------------------------------
// Facts and records of the model.

// Fact is a fact of msgs: a vote request `[type |-> "vote", src, term, lastLogIndex, lastLogTerm]`
// (R 218), a grant `[type |-> "grant", src, dst, term]` (R 261) or an ack `[type |-> "ack", src,
// dst, term, index]` (R 413). The fields a shape lacks are zero, so Go's == on Facts is TLA+'s
// equality of the records.
type Fact struct {
	Type         string
	Src          string
	Dst          string
	Term         int
	LastLogIndex int
	LastLogTerm  int
	Index        int
}

// AppendFact is a request to append, `[type |-> "append", src, dst, term, prevLogIndex,
// prevLogTerm, entries, commit]` (R 337-339). The binding builds them from reports and never
// keeps one in msgs (B 114-116).
type AppendFact struct {
	Src          string
	Dst          string
	Term         int
	PrevLogIndex int
	PrevLogTerm  int
	Entries      []Entry
	Commit       int
}

// VoteRec is `[voter |-> i, term |-> t, cand |-> c]` (R 254).
type VoteRec struct {
	Voter string
	Term  int
	Cand  string
}

// LeaderRec is `[server |-> i, term |-> t]` (R 292).
type LeaderRec struct {
	Server string
	Term   int
}

// Confirmed is `[term |-> t, index |-> k]` (R 98-99).
type Confirmed struct {
	Term  int
	Index int
}

func factsHas(s []Fact, f Fact) bool {
	for _, g := range s {
		if g == f {
			return true
		}
	}
	return false
}

// factsAdd is `s \cup {f}`.
func factsAdd(s []Fact, f Fact) []Fact {
	if factsHas(s, f) {
		return s
	}
	out := make([]Fact, 0, len(s)+1)
	out = append(out, s...)
	return append(out, f)
}

// factsUnion is `s \cup t`.
func factsUnion(s, t []Fact) []Fact {
	out := s
	for _, f := range t {
		out = factsAdd(out, f)
	}
	return out
}

// factsMinus is `s \ t`.
func factsMinus(s, t []Fact) []Fact {
	var out []Fact
	for _, f := range s {
		if !factsHas(t, f) {
			out = append(out, f)
		}
	}
	return out
}

func votesHas(s []VoteRec, v VoteRec) bool {
	for _, w := range s {
		if w == v {
			return true
		}
	}
	return false
}

func votesAdd(s []VoteRec, v VoteRec) []VoteRec {
	if votesHas(s, v) {
		return s
	}
	out := make([]VoteRec, 0, len(s)+1)
	out = append(out, s...)
	return append(out, v)
}

func votesUnion(s, t []VoteRec) []VoteRec {
	out := s
	for _, v := range t {
		out = votesAdd(out, v)
	}
	return out
}

func votesMinus(s, t []VoteRec) []VoteRec {
	var out []VoteRec
	for _, v := range s {
		if !votesHas(t, v) {
			out = append(out, v)
		}
	}
	return out
}

func leadersHas(s []LeaderRec, l LeaderRec) bool {
	for _, m := range s {
		if m == l {
			return true
		}
	}
	return false
}

func leadersAdd(s []LeaderRec, l LeaderRec) []LeaderRec {
	if leadersHas(s, l) {
		return s
	}
	out := make([]LeaderRec, 0, len(s)+1)
	out = append(out, s...)
	return append(out, l)
}

// ---------------------------------------------------------------------------------------------
// Functions on terms.

// TermLog is one point of a function from terms to logs.
type TermLog struct {
	T int
	L []Entry
}

// TermLogs is a function from terms to logs (ledLog), sorted by term.
type TermLogs []TermLog

// Has is `t \in DOMAIN f`.
func (f TermLogs) Has(t int) bool {
	for _, p := range f {
		if p.T == t {
			return true
		}
	}
	return false
}

// Get is `f[t]`: an EvalError outside the domain.
func (f TermLogs) Get(t int) []Entry {
	for _, p := range f {
		if p.T == t {
			return p.L
		}
	}
	evalError("ledLog applied outside its domain")
	return nil
}

// With is `[u \in DOMAIN f \cup {t} |-> IF u = t THEN l ELSE f[u]]` (R 265 `WithLed`, B 136
// `LedWith`).
func (f TermLogs) With(t int, l []Entry) TermLogs {
	out := make(TermLogs, 0, len(f)+1)
	done := false
	for _, p := range f {
		if !done && t <= p.T {
			out = append(out, TermLog{T: t, L: l})
			done = true
			if p.T == t {
				continue
			}
		}
		out = append(out, p)
	}
	if !done {
		out = append(out, TermLog{T: t, L: l})
	}
	return out
}

// Without is `[t \in DOMAIN f \ S |-> f[t]]`.
func (f TermLogs) Without(s []int) TermLogs {
	var out TermLogs
	for _, p := range f {
		if !intsHas(s, p.T) {
			out = append(out, p)
		}
	}
	return out
}

// TermConf is one point of a function from terms to configurations.
type TermConf struct {
	T int
	C Conf
}

// TermConfs is a function from terms to configurations (ledConf), sorted by term.
type TermConfs []TermConf

// Get is `f[t]`: an EvalError outside the domain.
func (f TermConfs) Get(t int) Conf {
	for _, p := range f {
		if p.T == t {
			return p.C
		}
	}
	evalError("ledConf applied outside its domain")
	return Conf{}
}

// With is R 266 `WithConf`.
func (f TermConfs) With(t int, c Conf) TermConfs {
	out := make(TermConfs, 0, len(f)+1)
	done := false
	for _, p := range f {
		if !done && t <= p.T {
			out = append(out, TermConf{T: t, C: c})
			done = true
			if p.T == t {
				continue
			}
		}
		out = append(out, p)
	}
	if !done {
		out = append(out, TermConf{T: t, C: c})
	}
	return out
}

// Without is `[t \in DOMAIN f \ S |-> f[t]]`.
func (f TermConfs) Without(s []int) TermConfs {
	var out TermConfs
	for _, p := range f {
		if !intsHas(s, p.T) {
			out = append(out, p)
		}
	}
	return out
}

// TermInt is one point of a function from terms to integers.
type TermInt struct {
	T int
	V int
}

// TermInts is a function from terms to integers (ledAt, elAt, termLen), sorted by term.
type TermInts []TermInt

// Has is `t \in DOMAIN f`.
func (f TermInts) Has(t int) bool {
	for _, p := range f {
		if p.T == t {
			return true
		}
	}
	return false
}

// Get is `f[t]`: an EvalError outside the domain.
func (f TermInts) Get(t int) int {
	for _, p := range f {
		if p.T == t {
			return p.V
		}
	}
	evalError("a function on terms applied outside its domain")
	return 0
}

// With is R 267 `With(f, t, k)`.
func (f TermInts) With(t int, v int) TermInts {
	out := make(TermInts, 0, len(f)+1)
	done := false
	for _, p := range f {
		if !done && t <= p.T {
			out = append(out, TermInt{T: t, V: v})
			done = true
			if p.T == t {
				continue
			}
		}
		out = append(out, p)
	}
	if !done {
		out = append(out, TermInt{T: t, V: v})
	}
	return out
}

// Without is `[t \in DOMAIN f \ S |-> f[t]]`.
func (f TermInts) Without(s []int) TermInts {
	var out TermInts
	for _, p := range f {
		if !intsHas(s, p.T) {
			out = append(out, p)
		}
	}
	return out
}

func intsHas(s []int, x int) bool {
	for _, y := range s {
		if y == x {
			return true
		}
	}
	return false
}
