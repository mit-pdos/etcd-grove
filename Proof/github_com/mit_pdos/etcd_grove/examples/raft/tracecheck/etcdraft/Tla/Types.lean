/-
Lean-first (no Rocq counterpart).

# raft's TLA+ specification in Lean: values (2026-11-08)

The Lean transcription of `etcdraft.tla` and `Traceetcdraft.tla` (etcd-io/raft's `tla/`, at the
raft this repository verifies), Draft S2 of `notes/trace-validation-plan.md`. It mirrors the Go
transcription (`examples/raft/tracecheck/etcdraft`, package `etcdraft`) definition by
definition, with the Go's names, so that the proof that the Go checker computes what these
definitions say (layer C) follows the Go function by function; each definition's comment names
the TLA+ definition it transcribes. What the closed theorem means rests on one transcription of
the TLA+, the Go one or this one, which layer C proves equal (the plan's "Trust base").

Values, as the Go's:

- a server is a `Nat` (the trace's strings "1", "2", ... are the numbers they denote; Nil, "0", is
  0); a set of servers is a sorted list without duplicates (`SetIds`), built only by `SetIds.mk`
  and the operations below, so that `=` on it is set equality;
- numbers are `Int` (TLA+'s, unbounded; the Go's are 64-bit `int`, which the checker's proof
  bounds);
- a log is a `List Entry` (TLA+'s sequences are 1-indexed: `log[k]` is `log[k-1]!` here);
- a message is a `Msg`, the fields of all four record shapes in one structure (a shape's absent
  fields always at their default), so that `=` on messages is TLA+'s;
- a bag of messages is a `Bag`, its distinct messages with their counts.

Everything is computable (`deriving DecidableEq`), so the definitions run on traces.
-/
module

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-- A server; `nil` (0) is TLA+'s `Nil`. -/
abbrev ID := Nat

def nil : ID := 0

/-- A server's state: TLA+'s constants `Follower`, `Candidate`, `Leader`, whose values are the
trace's role strings (`Traceetcdraft.cfg`); any other role string is a value of its own. -/
abbrev Role := String

def follower : Role := "StateFollower"
def candidate : Role := "StateCandidate"
def leader : Role := "StateLeader"
/-- The constant `PreCandidate` (reached only with `PreVote`). -/
def preCandidate : Role := "StatePreCandidate"

/-! ## Sets of servers -/

/-- A finite set of servers, as a sorted list without duplicates (Go: `Set`). -/
abbrev SetIds := List ID

/-- `insertSorted id s`: `s ∪ {id}` for a sorted, duplicate-free `s` (Go: `NewSet`'s insertion). -/
def insertSorted (id : ID) : SetIds → SetIds
  | [] => [id]
  | x :: xs => if id < x then id :: x :: xs else if id = x then x :: xs else x :: insertSorted id xs

/-- The set of `ids` (Go: `NewSet`). -/
def SetIds.mk (ids : List ID) : SetIds := ids.foldl (fun s id => insertSorted id s) []

/-- `s ∪ t` (Go: `Set.Union`). -/
def SetIds.union (s t : SetIds) : SetIds := SetIds.mk (s ++ t)

/-- `s ∪ {id}` (Go: `Set.Add`). -/
def SetIds.add (s : SetIds) (id : ID) : SetIds := s.union [id]

/-- `s \ t` (Go: `Set.Minus`). -/
def SetIds.minus (s t : SetIds) : SetIds := s.filter (fun id => !t.contains id)

/-- `s \ {id}` (Go: `Set.Remove`). -/
def SetIds.remove (s : SetIds) (id : ID) : SetIds := s.minus [id]

/-- `s ⊆ t` (Go: `Set.Subset`). -/
def SetIds.subset (s t : SetIds) : Bool := s.all (fun id => t.contains id)

/-- `q \in Quorum(c)`: `Quorum(c) == {i \in SUBSET(c) : Cardinality(i) * 2 > Cardinality(c)}`
(Go: `IsQuorum`). -/
def isQuorum (q c : SetIds) : Bool := q.subset c && decide (q.length * 2 > c.length)

/-! ## Log entries -/

/-- A log entry's type: TLA+'s constants `ValueEntry`, `ConfigEntry`. -/
inductive EntryType where
  | value | config
  deriving DecidableEq, Repr, Inhabited

/-- An entry's value: `[val |-> v]` (a client request's), `<<>>` (the empty value a leader
appends in place of a refused configuration change), `[newconf |-> ..., learners |-> ...]` (a
configuration entry's). -/
inductive Value where
  | val (v : Int)
  | emptySeq
  | conf (newconf learners : SetIds)
  deriving DecidableEq, Repr, Inhabited

/-- A log entry, `[term |-> ..., type |-> ..., value |-> ...]`. -/
structure Entry where
  term : Int
  type : EntryType
  value : Value
  deriving DecidableEq, Repr, Inhabited

/-- `SubSeq(s, m, n)` where it is defined: `some` of `s`'s elements `m..n` (1-indexed), the empty
sequence when `m > n`, and `none` where TLC fails (`m ≤ n` with `m < 1` or `n > Len(s)`; the Go
panics with an `EvalError`). -/
def subSeq (s : List Entry) (m n : Int) : Option (List Entry) :=
  if m > n then some []
  else if m < 1 ∨ n > s.length then none
  else some ((s.drop (m.toNat - 1)).take (n.toNat - m.toNat + 1))

/-- `LastTerm(xlog) == IF xlog = <<>> THEN 0 ELSE xlog[Len(xlog)].term`. -/
def lastTerm (xlog : List Entry) : Int :=
  match xlog.getLast? with
  | none => 0
  | some e => e.term

/-- SequencesExt's `IsPrefix(s, t)`. -/
def isPrefix (s t : List Entry) : Bool := s.length ≤ t.length && (t.take s.length == s)

/-! ## Messages -/

/-- A message's type: TLA+'s constants `RequestVoteRequest`, `RequestVoteResponse`,
`AppendEntriesRequest`, `AppendEntriesResponse`. -/
inductive MsgType where
  | requestVoteRequest | requestVoteResponse | appendEntriesRequest | appendEntriesResponse
  | preVoteRequest | preVoteResponse
  deriving DecidableEq, Repr, Inhabited

/-- A message, any of the specification's four record shapes (a shape's absent fields at their
default, as the Go's `Msg`):

- `RequestVoteRequest`: mtype, mterm, mlastLogTerm, mlastLogIndex, msource, mdest;
- `RequestVoteResponse`: mtype, mterm, mvoteGranted, msource, mdest;
- `AppendEntriesRequest`: mtype, msubtype, mterm, mprevLogIndex, mprevLogTerm, mentries,
  mcommitIndex, msource, mdest;
- `AppendEntriesResponse`: mtype, msubtype, mterm, msuccess, mmatchIndex, msource, mdest. -/
structure Msg where
  type : MsgType
  subtype : String := ""
  term : Int
  lastLogTerm : Int := 0
  lastLogIndex : Int := 0
  voteGranted : Bool := false
  prevLogIndex : Int := 0
  prevLogTerm : Int := 0
  entries : List Entry := []
  commitIndex : Int := 0
  success : Bool := false
  matchIndex : Int := 0
  source : ID
  dest : ID
  deriving DecidableEq, Repr, Inhabited

/-! ## Bags of messages -/

/-- A bag (multiset) of messages, as its distinct messages with their counts, each count positive
(Go: `Bag`). Two bags are equal as bags when `Bag.eq` holds (the lists may differ in order). -/
abbrev Bag := List (Msg × Nat)

/-- `IF m \in DOMAIN b THEN b[m] ELSE 0` (Go: `Bag.Count`). -/
def Bag.count (b : Bag) (m : Msg) : Nat :=
  match b.find? (fun it => it.1 == m) with
  | some it => it.2
  | none => 0

/-- `DOMAIN b` (Go: `Bag.Domain`). -/
def Bag.domain (b : Bag) : List Msg := b.map Prod.fst

/-- `b` with `n` more of `m` (Go: `Bag.add`). -/
def Bag.add (b : Bag) (m : Msg) (n : Nat) : Bag :=
  if b.any (fun it => it.1 == m) then b.map (fun it => if it.1 == m then (it.1, it.2 + n) else it)
  else b ++ [(m, n)]

/-- `b` with `n` fewer of `m`, none below zero (Go: `Bag.sub`). -/
def Bag.sub (b : Bag) (m : Msg) (n : Nat) : Bag :=
  b.filterMap (fun it => if it.1 == m then (if it.2 > n then some (it.1, it.2 - n) else none) else some it)

/-- `WithMessage(m, b) == b (+) SetToBag({m})` (Go: `Bag.With`). -/
def Bag.with (b : Bag) (m : Msg) : Bag := b.add m 1

/-- `WithoutMessage(m, b) == b (-) SetToBag({m})` (Go: `Bag.Without`). -/
def Bag.without (b : Bag) (m : Msg) : Bag := b.sub m 1

/-- The sub-bag of `b`'s messages satisfying `p`, with their counts (Go: `Bag.Filter`). -/
def Bag.filterMsgs (b : Bag) (p : Msg → Bool) : Bag := b.filter (fun it => p it.1)

/-- `b (+) c` (Go: `Bag.Plus`). -/
def Bag.plus (b c : Bag) : Bag := c.foldl (fun acc it => acc.add it.1 it.2) b

/-- `b (-) c` (Go: `Bag.Minus`). -/
def Bag.minus (b c : Bag) : Bag := c.foldl (fun acc it => acc.sub it.1 it.2) b

/-- `b = c` as bags (Go: `Bag.Equal`). -/
def Bag.eq (b c : Bag) : Bool := b.length == c.length && b.all (fun it => c.count it.1 == it.2)

end Etcdraft
end EtcdGrove
end Perennial
