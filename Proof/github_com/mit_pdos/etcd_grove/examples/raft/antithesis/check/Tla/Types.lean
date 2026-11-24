/-
Lean-first (no Rocq counterpart).

# Antithesis's TLA+ model of raft in Lean: values (#33 S3b, 2026-11-23)

The Lean transcription of Antithesis's `EtcdRaft.tla` and `EtcdBinding.tla` (vendored under
`third_party/etcd-raft-formalized/spec/`, cited as R and B with line numbers), stage S3b of
mit-pdos/etcd-grove#33 (`notes/antithesis-check-design.md`, §10). As tracecheck's
(`Proof/.../tracecheck/etcdraft/Tla/`), it mirrors the Go transcription (`examples/raft/
antithesis/check`, package `check`) definition by definition, with the Go's names, so that the
proof that the Go checker computes what these definitions say follows the Go function by
function; each definition's comment names the TLA+ definition it transcribes. What the closed
theorem means rests on one transcription of the TLA+, the Go one or this one, which the
checker's proof shows equal on the streams its premise admits (§10 of the design note).

Values, as the Go's:

- a string (a server's name, a role, a type tag) is a `GoString` (Perennial's byte list, the very
  value a Go string is), so the checker's specs relate strings by equality; `Nil` is the empty
  string;
- numbers are `Int` (TLA+'s, unbounded; the Go's are 64-bit `int`, which the checker's spec
  bounds, `Stream.Bounded`);
- a set of servers is a sorted (`go.GoStringLt`) list without duplicates (`SSet`), built only by
  `setAdd` and the operations below, so that `=` on it is set equality;
- a sequence is a `List` (TLA+'s `s[k]` is `s[k-1]`); a record a structure; a function on `Server`
  a list indexed like `Config.server`; a function on terms a list of (term, value) pairs sorted by
  term (`TermFn`);
- a report's optional field is an `Option` (TLA+'s `"f" \in DOMAIN ev`; the Go's `Has` bits).

Where TLC stops with an evaluation error (the Go panics with an `EvalError`), a definition is in
`EvalM := Except String`. Conjunctions are evaluated in the Go's (= the TLA+'s) order: `andM a b`
is `b` only when `a` is `true`, so an error in `b` counts only where the TLA+ evaluates `b`.

Everything is computable, so the definitions run on streams (`AntCheck.Tests`).
-/
module

public import Perennial.Golang.Defn.String

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

/-- Where TLC stops with an evaluation error (Go: a panic with an `EvalError`). -/
abbrev EvalM := Except String

/-- An evaluation error (Go: `evalError`). -/
def evalError {α : Type} (what : String) : EvalM α := throw what

/-- `a /\ b`, `b` evaluated only where `a` holds (Go: `&&`). -/
def andM (a b : EvalM Bool) : EvalM Bool := do if (← a) then b else pure false

/-- `a \/ b`, `b` evaluated only where `a` does not hold (Go: `||`). -/
def orM (a b : EvalM Bool) : EvalM Bool := do if (← a) then pure true else b

/-- A string of the stream or the model (Go: `string`). -/
abbrev Str := GoString

/-! ## Sets of servers (Go: `Set`) -/

/-- A finite set of server names: sorted by `go.GoStringLt`, without duplicates. -/
abbrev SSet := List Str

/-- Go: `strLess`, `a < b` on strings. -/
def strLess (a b : Str) : Bool := decide (go.GoStringLt a b)

/-- `s \cup {x}` (Go: `SetAdd`): `x` inserted before the first element not below it. -/
def setAdd (s : SSet) (x : Str) : SSet :=
  let k := (s.takeWhile (fun y => strLess y x)).length
  if s[k]? = some x then s else s.take k ++ x :: s.drop k

/-- R 138 `Range(s)`, the set of a sequence's elements (Go: `SetOf`). -/
def setOf (xs : List Str) : SSet := xs.foldl setAdd []

/-- `x \in s` (Go: `Set.Has`). -/
def SSet.has (s : SSet) (x : Str) : Bool := s.contains x

/-- `s \cup t` (Go: `Set.Union`). -/
def SSet.union (s t : SSet) : SSet := t.foldl setAdd s

/-- `s \ t` (Go: `Set.Minus`). -/
def SSet.minus (s t : SSet) : SSet := s.filter (fun x => !t.has x)

/-- `Cardinality(s \cap t)` (Go: `interCount`). -/
def interCount (s t : SSet) : Nat := (s.filter (fun x => t.has x)).length

/-! ## Entries and logs -/

/-- An entry's value (Go: `Value`): a string (a command's payload, `""` for the others), or for a
`"conf"` entry the record `[add, remove, joint, leave]` (R 136-137). -/
structure Value where
  isRec : Bool := false
  str : Str := []
  add : List Str := []
  remove : List Str := []
  joint : Bool := false
  leave : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- `v = w`; TLC cannot compare a string with a record (Go: `Value.Equal`). -/
def Value.equal (v w : Value) : EvalM Bool :=
  if v.isRec ≠ w.isRec then evalError "a string compared with a record (an entry's value)"
  else if !v.isRec then pure (v.str == w.str)
  else pure (v.add == w.add && v.remove == w.remove && v.joint == w.joint && v.leave == w.leave)

/-- `v` read as a record (Go: `Value.rec`). -/
def Value.asRec (v : Value) : EvalM Value :=
  if !v.isRec then evalError "a field of a string (an entry's value read as a change)" else pure v

/-- R 133 `Entry`: `[term |-> t, type |-> ty, value |-> v]`. -/
structure Entry where
  term : Int
  type : Str
  value : Value
  deriving DecidableEq, Repr, Inhabited

/-- `e = f` (Go: `Entry.Equal`). -/
def Entry.equal (e f : Entry) : EvalM Bool :=
  if e.term ≠ f.term ∨ e.type ≠ f.type then pure false else e.value.equal f.value

/-- Elementwise `=`, stopping at the first difference (Go: `EntriesEqual`'s loop). -/
def entriesEqualAux : List Entry → List Entry → EvalM Bool
  | a :: xs, b :: ys => do if !(← a.equal b) then pure false else entriesEqualAux xs ys
  | _, _ => pure true

/-- `a = b` on sequences of entries (Go: `EntriesEqual`). -/
def entriesEqual (a b : List Entry) : EvalM Bool :=
  if a.length ≠ b.length then pure false else entriesEqualAux a b

/-- `l[k]`, an error outside `1..Len(l)` (Go: `At`). -/
def atE (l : List Entry) (k : Int) : EvalM Entry :=
  if k < 1 ∨ k > l.length then evalError "a sequence of entries applied outside its domain"
  else pure (l[(k - 1).toNat]!)

/-- `SubSeq(s, m, n)` (Go: `SubSeq`): `<<>>` when `m > n`, else `s[m..n]`, an error outside
`1..Len(s)`. -/
def subSeq (s : List Entry) (m n : Int) : EvalM (List Entry) :=
  if m > n then pure []
  else if m < 1 ∨ n > s.length then evalError "SubSeq outside the sequence"
  else pure ((s.drop (m - 1).toNat).take (n - m + 1).toNat)

/-- R 130 `IsPrefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))`. -/
def isPrefix (a b : List Entry) : EvalM Bool :=
  if a.length ≤ b.length then do entriesEqual a (← subSeq b 1 a.length) else pure false

/-- R 131 `TermAt(l, k) == IF k > 0 /\ k <= Len(l) THEN l[k].term ELSE 0`. -/
def termAt (l : List Entry) (k : Int) : Int :=
  if k > 0 ∧ k ≤ l.length then (l[(k - 1).toNat]!).term else 0

/-- R 125 `Min`. -/
def imin (a b : Int) : Int := if a ≤ b then a else b

/-- R 126 `Max`. -/
def imax (a b : Int) : Int := if a ≥ b then a else b

/-! ## Configurations -/

/-- A configuration `[in |-> ..., out |-> ...]` (R 95-96; Go: `Conf`). -/
structure Conf where
  cin : SSet := []
  cout : SSet := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Facts and records of the model -/

/-- A fact of `msgs` (Go: `Fact`): a vote request `[type |-> "vote", src, term, lastLogIndex,
lastLogTerm]` (R 218), a grant `[type |-> "grant", src, dst, term]` (R 261) or an ack
`[type |-> "ack", src, dst, term, index]` (R 413); the fields a shape lacks are zero, so `=` is
TLA+'s equality of the records. -/
structure Fact where
  type : Str
  src : Str := []
  dst : Str := []
  term : Int := 0
  lastLogIndex : Int := 0
  lastLogTerm : Int := 0
  index : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- A request to append (R 337-339; Go: `AppendFact`), built from reports, never kept in `msgs`. -/
structure AppendFact where
  src : Str
  dst : Str
  term : Int
  prevLogIndex : Int
  prevLogTerm : Int
  entries : List Entry
  commit : Int
  deriving DecidableEq, Repr, Inhabited

/-- `[voter |-> i, term |-> t, cand |-> c]` (R 254; Go: `VoteRec`). -/
structure VoteRec where
  voter : Str
  term : Int
  cand : Str
  deriving DecidableEq, Repr, Inhabited

/-- `[server |-> i, term |-> t]` (R 292; Go: `LeaderRec`). -/
structure LeaderRec where
  server : Str
  term : Int
  deriving DecidableEq, Repr, Inhabited

/-- `[term |-> t, index |-> k]` (R 98-99; Go: `Confirmed`). -/
structure Confirmed where
  term : Int := 0
  index : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- A set of records kept as a list without duplicates, insertion order (Go: `factsAdd`,
`votesAdd`, `leadersAdd`): `s \cup {x}`. -/
def lset.add {α : Type} [DecidableEq α] (s : List α) (x : α) : List α :=
  if s.contains x then s else s ++ [x]

/-- `s \cup t` (Go: `factsUnion`, `votesUnion`). -/
def lset.union {α : Type} [DecidableEq α] (s t : List α) : List α := t.foldl lset.add s

/-- `s \ t` (Go: `factsMinus`, `votesMinus`). -/
def lset.minus {α : Type} [DecidableEq α] (s t : List α) : List α := s.filter (fun x => !t.contains x)

/-! ## Functions on terms (Go: `TermLogs`, `TermConfs`, `TermInts`) -/

/-- A function from terms, as its points sorted by term. -/
abbrev TermFn (α : Type) := List (Int × α)

/-- `t \in DOMAIN f`. -/
def TermFn.has {α : Type} (f : TermFn α) (t : Int) : Bool := f.any (fun p => p.1 == t)

/-- `f[t]`, an error outside the domain. -/
def TermFn.get {α : Type} (f : TermFn α) (t : Int) : EvalM α :=
  match f.find? (fun p => p.1 == t) with
  | some p => pure p.2
  | none => evalError "a function on terms applied outside its domain"

/-- `[u \in DOMAIN f \cup {t} |-> IF u = t THEN v ELSE f[u]]` (R 265-267 `WithLed`, `WithConf`,
`With`; B 136 `LedWith`). -/
def TermFn.with {α : Type} : TermFn α → Int → α → TermFn α
  | [], t, v => [(t, v)]
  | p :: ps, t, v =>
    if t ≤ p.1 then (t, v) :: (if p.1 = t then ps else p :: ps) else p :: TermFn.with ps t v

/-- `[t \in DOMAIN f \ S |-> f[t]]`. -/
def TermFn.without {α : Type} (f : TermFn α) (s : List Int) : TermFn α :=
  f.filter (fun p => !s.contains p.1)

/-! ## Reports (Go: `event.go`) -/

/-- A reported message (Go: `Msg`), `{type, from, to, term, index, logTerm, entries, commit,
reject, hint}` (rawnode's package comment); a field the report lacks is `none` (Go: its `Has`
bit clear), and reading it is an evaluation error, as in TLC. (`hint` is never read.) -/
structure Msg where
  type : Option Str := none
  frm : Option Str := none
  to : Option Str := none
  term : Option Int := none
  index : Option Int := none
  logTerm : Option Int := none
  entries : Option (List Entry) := none
  commit : Option Int := none
  reject : Option Bool := none
  deriving DecidableEq, Repr, Inhabited

/-- A field of a report: an evaluation error if absent (Go: `need`). -/
def need {α : Type} : Option α → EvalM α
  | some a => pure a
  | none => evalError "a field the report does not have"

/-- A report's `snap`: `{index, term}` (Go: `SnapRef`). -/
structure SnapRef where
  index : Int := 0
  term : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- One report of the stream (Go: `Event`; TraceKit's `StreamEvent(i)`). The fields the binding
never reads are dropped; `bad`, if not empty, says why the line is not a record of the shape the
binding reads (processing it is an evaluation error). `b` and `a` are the presence of the fields
`b`, `a`, whose values the binding never reads. -/
structure Event where
  e : Str
  node : Str
  byE : Option Str := none
  role : Option Str := none
  term : Option Int := none
  vote : Option Str := none
  commit : Option Int := none
  first : Option Int := none
  entries : Option (List Entry) := none
  lastIndex : Option Int := none
  lastTerm : Option Int := none
  applied : Option Int := none
  voters : Option (List Str) := none
  outgoing : Option (List Str) := none
  snap : Option SnapRef := none
  msg : Option Msg := none
  cause : Option (List Msg) := none
  b : Bool := false
  a : Bool := false
  w : Option Int := none
  more : Option Int := none
  index : Option Int := none
  ctx : Option Str := none
  bad : Str := []
  deriving DecidableEq, Repr, Inhabited

/-- `C[1]` for a sequence of messages, an error on `<<>>` (Go: `msgSeqHead`). -/
def msgSeqHead : List Msg → EvalM Msg
  | m :: _ => pure m
  | [] => evalError "<<>>[1]"

/-! ## The binding's state (Go: `state.go`) -/

/-- The binding's constants (B 40-42, R 75-78; Go: `Config`). `Values = {"v"}` and `Nil = ""` are
fixed. -/
structure Config where
  server : SSet
  initVoters : SSet
  bootstrapped : Bool
  deriving DecidableEq, Repr, Inhabited

/-- What an announced write keeps to be taken back (B 349-359 `pre`; Go: `Pre`). -/
structure Pre where
  term : Int := 0
  voteTerm : Int := 0
  voteFor : Str := []
  commit : Int := 0
  keep : Int := 0
  suffix : List Entry := []
  confirmed : Confirmed := {}
  msgs : List Fact := []
  votes : List VoteRec := []
  acks : List Fact := []
  low : Int := 0
  made : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A queued report (B 441, 452; Go: `QItem`): the report and the message being handled. -/
structure QItem where
  ev : Event
  m : List Msg
  deriving DecidableEq, Repr, Inhabited

/-- A read index asked for (B 658; Go: `ReadRec`). -/
structure ReadRec where
  ctx : Str
  floor : Int
  deriving DecidableEq, Repr, Inhabited

/-- A state of the binding (B 44-54 with R 89-116; Go: `State`): every variable but `commits`,
`applied` and `read`, which the binding never changes and nothing it evaluates reads. Per-server
variables are lists indexed like `cfg.server`. -/
structure State where
  cfg : Config
  currentTerm : List Int
  voteTerm : List Int
  voteFor : List Str
  log : List (List Entry)
  commitIndex : List Int
  role : List Str
  lastApplied : List Int
  config : List Conf
  confAt : List Int
  confirmed : List Confirmed
  msgs : List Fact
  votes : List VoteRec
  leaders : List LeaderRec
  ledLog : TermFn (List Entry)
  ledConf : TermFn Conf
  ledAt : TermFn Int
  elAt : TermFn Int
  i : Int
  /-- `none`: `NoWrite` (`<<>>`); `some p`: `LastWrite(p)` (`<<p>>`). -/
  undo : List (Option Pre)
  pending : List (List Msg)
  queue : List (List QItem)
  reads : List (List ReadRec)
  chain : List Entry
  termLen : TermFn Int
  viol : SSet
  deriving DecidableEq, Repr, Inhabited

/-- The role names (R 85-87). -/
def follower : Str := go!"follower"
def candidate : Str := go!"candidate"
def leader : Str := go!"leader"

/-- The position of server `n` in `cfg.server`; a function on `Server` applied to a name outside
it is an evaluation error (Go: `State.idx`). -/
def State.idx (s : State) (n : Str) : EvalM Nat :=
  match s.cfg.server.idxOf? n with
  | some k => pure k
  | none => evalError "a function on Server applied to a name that is not a server"

/-- R 140 `InitConf == [in |-> InitVoters, out |-> {}]`. -/
def Config.initConf (cfg : Config) : Conf := { cin := cfg.initVoters, cout := [] }

/-- B 755-764 `Init0` (Go: `Init0`): `BootInit` (B 733-753) when `Bootstrapped`, else the model's
`Init` (R 181-201). `First == CHOOSE s \in InitVoters : TRUE` (B 731) is the least element, as
TLC chooses; with no voter it is undefined (the Go indexes an empty slice). -/
def init0 (cfg : Config) : EvalM State := do
  let n := cfg.server.length
  let base : State :=
    { cfg, currentTerm := List.replicate n 0, voteTerm := List.replicate n 0,
      voteFor := List.replicate n [], log := List.replicate n [],
      commitIndex := List.replicate n 0, role := List.replicate n follower,
      lastApplied := List.replicate n 0, config := List.replicate n cfg.initConf,
      confAt := List.replicate n 0, confirmed := List.replicate n {},
      msgs := [], votes := [], leaders := [], ledLog := [], ledConf := [], ledAt := [], elAt := [],
      i := 1, undo := List.replicate n none, pending := List.replicate n [],
      queue := List.replicate n [], reads := List.replicate n [], chain := [], termLen := [],
      viol := [] }
  if !cfg.bootstrapped then return base
  match cfg.initVoters with
  | [] => evalError "First: CHOOSE from an empty InitVoters"
  | first :: _ =>
    let boot : List Entry := [{ term := 1, type := go!"config", value := { str := [] } }]
    return { base with
      currentTerm := List.replicate n 1, voteTerm := List.replicate n 1,
      voteFor := List.replicate n first, log := List.replicate n boot,
      confirmed := List.replicate n { term := 1, index := 1 },
      leaders := [{ server := first, term := 1 }], ledLog := [(1, boot)],
      ledConf := [(1, cfg.initConf)], ledAt := [(1, 0)], elAt := [(1, 0)] }

end AntCheck
end EtcdGrove
end Perennial
