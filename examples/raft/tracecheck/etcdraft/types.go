// Package etcdraft is a transcription into Go of raft's TLA+ specification (`tla/etcdraft.tla` of
// etcd-io/raft, at the raft this repository verifies) and of its trace specification
// (`tla/Traceetcdraft.tla`), for checking raft's traces: directly (CheckTrace, a breadth-first
// search like TLC's); porcupine checks with it in package pmodel, and package ndjson reads traces.
//
// The transcription follows the TLA+ text definition by definition, with the same names; each
// definition's comment quotes the TLA+ name it transcribes. TLA+'s values become Go values:
//
//   - a server is an ID (the TLA+ specification's servers are the trace's strings "1", "2", ...;
//     an ID is the number such a string denotes; Nil, "0", is 0);
//   - a set of servers is a Set, a sorted slice without duplicates;
//   - a log is a []Entry (TLA+'s sequences are 1-indexed: log[i][k] is Log[k-1]);
//   - a message is a Msg, the fields of all four record shapes in one struct (a shape's absent
//     fields are always zero, so two messages are equal in Go when they are equal in TLA+);
//   - a bag of messages is a Bag, its distinct messages with their counts.
//
// Values are never written once built: an action builds its successor state by copying what it
// changes (State.clone and the mut* methods).
//
// What a proof of CheckTrace goes through (notes/trace-validation-plan.md, layer C) uses only
// slices, maps, structural equality and panics: no fmt, strings, sort or hashing; those are only in
// the String and Error methods, for messages and debugging.
package etcdraft

import (
	"fmt"
	"strconv"
	"strings"
)

// ID is a server. Nil is no server.
type ID = uint64

// Nil is TLA+'s Nil ("0" in the trace).
const Nil ID = 0

// Role is a server's state: TLA+'s constants Follower, Candidate, Leader, whose values are the
// trace's role strings (Traceetcdraft.cfg). A role is its string, so that a role string the trace
// has and these are not (raft's "StatePreCandidate", say) is a value of its own, equal only to
// itself, as in TLA+.
type Role string

const (
	Follower  Role = "StateFollower"
	Candidate Role = "StateCandidate"
	Leader    Role = "StateLeader"
)

func (r Role) String() string { return string(r) }

// ParseRole is the role a trace's role string denotes: the string itself.
func ParseRole(s string) Role { return Role(s) }

// EvalError is an evaluation error TLC would raise (a sequence indexed outside its domain): where
// TLC stops with an error, the transcription panics with an EvalError, which the checkers report
// (CheckTrace's Result.EvalError) as a failure. What names the evaluation, A, B, C its numbers.
type EvalError struct {
	What    string
	A, B, C int
}

func (e EvalError) Error() string {
	return fmt.Sprintf("TLC evaluation error: %s (%d, %d, %d)", e.What, e.A, e.B, e.C)
}

// evalError panics with an EvalError.
func evalError(what string, a, b, c int) {
	panic(EvalError{What: what, A: a, B: b, C: c})
}

// Set is a finite set of servers: sorted, without duplicates. A Set is never written.
type Set []ID

// NewSet is the set of ids (sorted by insertion: the sets of servers are small).
func NewSet(ids ...ID) Set {
	var out Set
	for _, id := range ids {
		k := 0
		for k < len(out) && out[k] < id {
			k++
		}
		if k < len(out) && out[k] == id {
			continue
		}
		out = append(out, 0)
		copy(out[k+1:], out[k:])
		out[k] = id
	}
	return out
}

// Has is `id \in s`.
func (s Set) Has(id ID) bool {
	for _, x := range s {
		if x == id {
			return true
		}
	}
	return false
}

// Union is `s \union t`.
func (s Set) Union(t Set) Set { return NewSet(append(append([]ID(nil), s...), t...)...) }

// Add is `s \union {id}`.
func (s Set) Add(id ID) Set { return s.Union(Set{id}) }

// Minus is `s \ t`.
func (s Set) Minus(t Set) Set {
	var out Set
	for _, id := range s {
		if !t.Has(id) {
			out = append(out, id)
		}
	}
	return out
}

// Remove is `s \ {id}`.
func (s Set) Remove(id ID) Set { return s.Minus(Set{id}) }

// Subset is `s \subseteq t`.
func (s Set) Subset(t Set) bool {
	for _, id := range s {
		if !t.Has(id) {
			return false
		}
	}
	return true
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

func (s Set) String() string {
	parts := make([]string, len(s))
	for k, id := range s {
		parts[k] = strconv.FormatUint(id, 10)
	}
	return "{" + strings.Join(parts, ",") + "}"
}

// IsQuorum is `q \in Quorum(c)`: `Quorum(c) == {i \in SUBSET(c) : Cardinality(i) * 2 >
// Cardinality(c)}`.
func IsQuorum(q, c Set) bool {
	return q.Subset(c) && len(q)*2 > len(c)
}

// EntryType is a log entry's type: TLA+'s constants ValueEntry, ConfigEntry.
type EntryType uint8

const (
	ValueEntry EntryType = iota
	ConfigEntry
)

// ValueKind is the shape of an entry's value: `[val |-> v]` (a client request's), `<<>>` (the
// empty value a leader appends in place of a refused configuration change), or `[newconf |-> ...,
// learners |-> ...]` (a configuration entry's).
type ValueKind uint8

const (
	ValRecord ValueKind = iota
	EmptySeq
	ConfRecord
)

// Value is a log entry's value.
type Value struct {
	Kind     ValueKind
	Val      int // ValRecord's val
	NewConf  Set // ConfRecord's newconf
	Learners Set // ConfRecord's learners
}

// Equal is `v = w`.
func (v Value) Equal(w Value) bool {
	return v.Kind == w.Kind && v.Val == w.Val && v.NewConf.Equal(w.NewConf) && v.Learners.Equal(w.Learners)
}

// Entry is a log entry, `[term |-> ..., type |-> ..., value |-> ...]`.
type Entry struct {
	Term  int
	Type  EntryType
	Value Value
}

// Equal is `e = f`.
func (e Entry) Equal(f Entry) bool {
	return e.Term == f.Term && e.Type == f.Type && e.Value.Equal(f.Value)
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

// IsPrefix is SequencesExt's `IsPrefix(s, t)`.
func IsPrefix(s, t []Entry) bool { return len(s) <= len(t) && EntriesEqual(s, t[:len(s)]) }

// SubSeq is `SubSeq(s, m, n)`: s's elements m..n (1-indexed), empty when m > n. It shares s's
// array (read only). With m <= n and an element missing (m < 1 or n > Len(s)) TLC fails, and so
// does SubSeq (an EvalError).
func SubSeq(s []Entry, m, n int) []Entry {
	if m > n {
		return nil
	}
	if m < 1 || n > len(s) {
		evalError("SubSeq past a sequence's end (length, from, to)", len(s), m, n)
	}
	return s[m-1 : n : n]
}

// LastTerm is `LastTerm(xlog) == IF xlog = <<>> THEN 0 ELSE xlog[Len(xlog)].term`.
func LastTerm(xlog []Entry) int {
	if len(xlog) == 0 {
		return 0
	}
	return xlog[len(xlog)-1].Term
}

// MsgType is a message's type: TLA+'s constants RequestVoteRequest, RequestVoteResponse,
// AppendEntriesRequest, AppendEntriesResponse.
type MsgType uint8

const (
	RequestVoteRequest MsgType = iota
	RequestVoteResponse
	AppendEntriesRequest
	AppendEntriesResponse
)

func (t MsgType) String() string {
	return [...]string{"RequestVoteRequest", "RequestVoteResponse", "AppendEntriesRequest", "AppendEntriesResponse"}[t]
}

// Msg is a message, any of the specification's four record shapes:
//
//	RequestVoteRequest:    mtype, mterm, mlastLogTerm, mlastLogIndex, msource, mdest
//	RequestVoteResponse:   mtype, mterm, mvoteGranted, msource, mdest
//	AppendEntriesRequest:  mtype, msubtype, mterm, mprevLogIndex, mprevLogTerm, mentries, mcommitIndex, msource, mdest
//	AppendEntriesResponse: mtype, msubtype, mterm, msuccess, mmatchIndex, msource, mdest
//
// A field its shape does not have is zero.
type Msg struct {
	Type         MsgType
	Subtype      string // "app", "heartbeat", "snapshot"
	Term         int
	LastLogTerm  int
	LastLogIndex int
	VoteGranted  bool
	PrevLogIndex int
	PrevLogTerm  int
	Entries      []Entry
	CommitIndex  int
	Success      bool
	MatchIndex   int
	Source, Dest ID
}

// Equal is `m = n` (structural: every field, the entries included).
func (m *Msg) Equal(n *Msg) bool {
	return m.Type == n.Type && m.Subtype == n.Subtype && m.Term == n.Term && m.LastLogTerm == n.LastLogTerm &&
		m.LastLogIndex == n.LastLogIndex && m.VoteGranted == n.VoteGranted && m.PrevLogIndex == n.PrevLogIndex &&
		m.PrevLogTerm == n.PrevLogTerm && m.CommitIndex == n.CommitIndex && m.Success == n.Success &&
		m.MatchIndex == n.MatchIndex && m.Source == n.Source && m.Dest == n.Dest && EntriesEqual(m.Entries, n.Entries)
}

func (m *Msg) String() string {
	switch m.Type {
	case RequestVoteRequest:
		return fmt.Sprintf("RVReq{%d->%d t%d last(%d,%d)}", m.Source, m.Dest, m.Term, m.LastLogTerm, m.LastLogIndex)
	case RequestVoteResponse:
		return fmt.Sprintf("RVResp{%d->%d t%d granted=%t}", m.Source, m.Dest, m.Term, m.VoteGranted)
	case AppendEntriesRequest:
		return fmt.Sprintf("AEReq{%s %d->%d t%d prev(%d,%d) n%d c%d}", m.Subtype, m.Source, m.Dest, m.Term,
			m.PrevLogIndex, m.PrevLogTerm, len(m.Entries), m.CommitIndex)
	}
	return fmt.Sprintf("AEResp{%s %d->%d t%d ok=%t match%d}", m.Subtype, m.Source, m.Dest, m.Term, m.Success, m.MatchIndex)
}

// Bag is a bag (multiset) of messages: Bags' `msg -> count`, DOMAIN its messages of positive
// count, held as a list of distinct messages with their counts. A Bag is never written once built:
// the operations return new bags.
type Bag struct {
	items []bagItem
}

type bagItem struct {
	msg   *Msg
	count int
}

// EmptyBag is Bags' EmptyBag.
var EmptyBag = Bag{}

// find is the position of m in b's items, or -1.
func (b Bag) find(m *Msg) int {
	for k, it := range b.items {
		if it.msg.Equal(m) {
			return k
		}
	}
	return -1
}

// Count is `IF m \in DOMAIN b THEN b[m] ELSE 0`.
func (b Bag) Count(m *Msg) int {
	if k := b.find(m); k >= 0 {
		return b.items[k].count
	}
	return 0
}

// Len is the number of distinct messages (Cardinality(DOMAIN b)).
func (b Bag) Len() int { return len(b.items) }

// Domain is `DOMAIN b` (in the order the messages came in).
func (b Bag) Domain() []*Msg {
	out := make([]*Msg, len(b.items))
	for k, it := range b.items {
		out[k] = it.msg
	}
	return out
}

// add is b with n more of m (n > 0).
func (b Bag) add(m *Msg, n int) Bag {
	items := append([]bagItem(nil), b.items...)
	if k := b.find(m); k >= 0 {
		items[k] = bagItem{msg: items[k].msg, count: items[k].count + n}
	} else {
		items = append(items, bagItem{msg: m, count: n})
	}
	return Bag{items: items}
}

// sub is b with n fewer of m (none below zero).
func (b Bag) sub(m *Msg, n int) Bag {
	k := b.find(m)
	if k < 0 {
		return b
	}
	var items []bagItem
	for h, it := range b.items {
		if h != k {
			items = append(items, it)
		} else if it.count > n {
			items = append(items, bagItem{msg: it.msg, count: it.count - n})
		}
	}
	return Bag{items: items}
}

// With is `WithMessage(m, b) == b (+) SetToBag({m})`.
func (b Bag) With(m *Msg) Bag { return b.add(m, 1) }

// Without is `WithoutMessage(m, b) == b (-) SetToBag({m})` (a message not in b leaves b as is).
func (b Bag) Without(m *Msg) Bag { return b.sub(m, 1) }

// Filter is the sub-bag of b's messages satisfying p, with their counts.
func (b Bag) Filter(p func(*Msg) bool) Bag {
	var items []bagItem
	for _, it := range b.items {
		if p(it.msg) {
			items = append(items, it)
		}
	}
	return Bag{items: items}
}

// Plus is `b (+) c`.
func (b Bag) Plus(c Bag) Bag {
	out := b
	for _, it := range c.items {
		out = out.add(it.msg, it.count)
	}
	return out
}

// Minus is `b (-) c` (counts below zero are zero).
func (b Bag) Minus(c Bag) Bag {
	out := b
	for _, it := range c.items {
		out = out.sub(it.msg, it.count)
	}
	return out
}

// Equal is `b = c`.
func (b Bag) Equal(c Bag) bool {
	if len(b.items) != len(c.items) {
		return false
	}
	for _, it := range b.items {
		if c.Count(it.msg) != it.count {
			return false
		}
	}
	return true
}
