// Package etcdraft is a transcription into Go of raft's TLA+ specification (`tla/etcdraft.tla` of
// etcd-io/raft, at the raft this repository verifies) and of its trace specification
// (`tla/Traceetcdraft.tla`), for checking raft's traces: directly (CheckTrace, a breadth-first
// search like TLC's) and with porcupine (Model).
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
//   - a bag of messages is a Bag, keyed by a canonical encoding of the message.
//
// Values are never written once built: an action builds its successor state by copying what it
// changes (State.clone and the mut* methods).
package etcdraft

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
)

// ID is a server. Nil is no server.
type ID = uint64

// Nil is TLA+'s Nil ("0" in the trace).
const Nil ID = 0

// Role is a server's state: TLA+'s constants Follower, Candidate, Leader, whose values are the
// trace's role strings (Traceetcdraft.cfg). RoleOther is any other role string, equal to none.
type Role uint8

const (
	Follower Role = iota
	Candidate
	Leader
	RoleOther
)

func (r Role) String() string {
	switch r {
	case Follower:
		return "StateFollower"
	case Candidate:
		return "StateCandidate"
	case Leader:
		return "StateLeader"
	}
	return "?"
}

// ParseRole is the role a trace's role string denotes.
func ParseRole(s string) Role {
	switch s {
	case "StateFollower":
		return Follower
	case "StateCandidate":
		return Candidate
	case "StateLeader":
		return Leader
	}
	return RoleOther
}

// Set is a finite set of servers: sorted, without duplicates. A Set is never written.
type Set []ID

// NewSet is the set of ids.
func NewSet(ids ...ID) Set {
	s := append(Set(nil), ids...)
	sort.Slice(s, func(a, b int) bool { return s[a] < s[b] })
	out := s[:0]
	for k, id := range s {
		if k == 0 || id != s[k-1] {
			out = append(out, id)
		}
	}
	return out
}

// Has is `id \in s`.
func (s Set) Has(id ID) bool {
	k := sort.Search(len(s), func(k int) bool { return s[k] >= id })
	return k < len(s) && s[k] == id
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
// array (read only). Where TLC would fail (m < 1 or n > Len(s) with m <= n: no such element), it
// keeps the elements that exist; the specification never asks for those in the traces checked so
// far (`Restart` after a log was truncated below its durable length could).
func SubSeq(s []Entry, m, n int) []Entry {
	m = max(m, 1)
	n = min(n, len(s))
	if m > n {
		return nil
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

// Key is a canonical encoding of m: two messages are equal exactly when their keys are.
func (m *Msg) Key() string {
	var b strings.Builder
	fmt.Fprintf(&b, "%d|%s|%d|%d|%d|%t|%d|%d|%d|%t|%d|%d|%d|", m.Type, m.Subtype, m.Term, m.LastLogTerm,
		m.LastLogIndex, m.VoteGranted, m.PrevLogIndex, m.PrevLogTerm, m.CommitIndex, m.Success, m.MatchIndex,
		m.Source, m.Dest)
	for _, e := range m.Entries {
		writeEntry(&b, e)
	}
	return b.String()
}

func writeEntry(b *strings.Builder, e Entry) {
	fmt.Fprintf(b, "(%d,%d,%d,%d,%v,%v)", e.Term, e.Type, e.Value.Kind, e.Value.Val, []ID(e.Value.NewConf), []ID(e.Value.Learners))
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
// count. A Bag is never written once built: the operations return new bags.
type Bag struct {
	items map[string]bagItem
}

type bagItem struct {
	msg   *Msg
	count int
}

// EmptyBag is Bags' EmptyBag.
var EmptyBag = Bag{}

// Count is `IF m \in DOMAIN b THEN b[m] ELSE 0`.
func (b Bag) Count(m *Msg) int { return b.items[m.Key()].count }

// CountKey is Count of the message whose key is k.
func (b Bag) CountKey(k string) int { return b.items[k].count }

// Len is the number of distinct messages (Cardinality(DOMAIN b)).
func (b Bag) Len() int { return len(b.items) }

// Domain is `DOMAIN b`, in key order.
func (b Bag) Domain() []*Msg {
	keys := make([]string, 0, len(b.items))
	for k := range b.items {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	out := make([]*Msg, len(keys))
	for n, k := range keys {
		out[n] = b.items[k].msg
	}
	return out
}

func (b Bag) copyItems() map[string]bagItem {
	items := make(map[string]bagItem, len(b.items)+1)
	for k, v := range b.items {
		items[k] = v
	}
	return items
}

// With is `WithMessage(m, b) == b (+) SetToBag({m})`.
func (b Bag) With(m *Msg) Bag {
	items := b.copyItems()
	k := m.Key()
	it := items[k]
	items[k] = bagItem{msg: m, count: it.count + 1}
	return Bag{items: items}
}

// Without is `WithoutMessage(m, b) == b (-) SetToBag({m})` (a message not in b leaves b as is).
func (b Bag) Without(m *Msg) Bag {
	k := m.Key()
	it, ok := b.items[k]
	if !ok {
		return b
	}
	items := b.copyItems()
	if it.count == 1 {
		delete(items, k)
	} else {
		items[k] = bagItem{msg: it.msg, count: it.count - 1}
	}
	return Bag{items: items}
}

// Filter is the sub-bag of b's messages satisfying p, with their counts.
func (b Bag) Filter(p func(*Msg) bool) Bag {
	items := map[string]bagItem{}
	for k, v := range b.items {
		if p(v.msg) {
			items[k] = v
		}
	}
	return Bag{items: items}
}

// Plus is `b (+) c`.
func (b Bag) Plus(c Bag) Bag {
	items := b.copyItems()
	for k, v := range c.items {
		it := items[k]
		items[k] = bagItem{msg: v.msg, count: it.count + v.count}
	}
	return Bag{items: items}
}

// Minus is `b (-) c` (counts below zero are zero).
func (b Bag) Minus(c Bag) Bag {
	items := b.copyItems()
	for k, v := range c.items {
		if it, ok := items[k]; ok {
			if it.count <= v.count {
				delete(items, k)
			} else {
				items[k] = bagItem{msg: it.msg, count: it.count - v.count}
			}
		}
	}
	return Bag{items: items}
}

// Equal is `b = c`.
func (b Bag) Equal(c Bag) bool {
	if len(b.items) != len(c.items) {
		return false
	}
	for k, v := range b.items {
		if c.items[k].count != v.count {
			return false
		}
	}
	return true
}

func (b Bag) key(sb *strings.Builder) {
	keys := make([]string, 0, len(b.items))
	for k := range b.items {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		fmt.Fprintf(sb, "[%s]x%d;", k, b.items[k].count)
	}
}
