/-
Lean-first (no Rocq counterpart).

# Antithesis's TLA+ model of raft in Lean: the operators of `EtcdRaft.tla` (#33 S3b)

The operators of `EtcdRaft.tla` (R) the binding uses (Go: `raft.go`); those that read the model's
variables take the state. See `Types.lean` for the conventions.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Types

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

/-- R 127 `Majority(S, V) == Cardinality(S \cap V) * 2 > Cardinality(V)`. -/
def majority (s v : SSet) : Bool := decide (interCount s v * 2 > v.length)

/-- R 129 `IsQuorum(S, C) == Majority(S, C.in) /\ (C.out = {} \/ Majority(S, C.out))`. -/
def isQuorum (s : SSet) (c : Conf) : Bool := majority s c.cin && (c.cout.length == 0 || majority s c.cout)

/-- R 139 `IsConf(e) == e.type = "conf"`. -/
def isConf (e : Entry) : Bool := e.type == go!"conf"

/-- R 142 `Target(C, d) == (C.in \cup Range(d.add)) \ Range(d.remove)`. -/
def target (c : Conf) (d : Value) : EvalM SSet := do
  let r ← d.asRec
  pure ((c.cin.union (setOf r.add)).minus (setOf r.remove))

/-- R 145-147 `NextConf`. -/
def nextConf (c : Conf) (d : Value) : EvalM Conf := do
  if (← d.asRec).leave then return { cin := c.cin, cout := [] }
  let t ← target c d
  if d.joint then return { cin := t, cout := c.cin }
  return { cin := t, cout := [] }

/-- R 152-156 `Legal`. -/
def legal (c : Conf) (d : Value) : EvalM Bool := do
  if (← d.asRec).leave then return c.cout.length != 0
  if c.cout.length != 0 then return false
  let t ← target c d
  if t.length == 0 then return false
  return d.joint || decide (((c.cin.minus t).union (t.minus c.cin)).length ≤ 1)

/-- R 161 `LastConf(l, a)`: the last index `k` in `1..a` with `IsConf(l[k])`, 0 for none. -/
def lastConf (l : List Entry) (a : Int) : EvalM Int :=
  (List.range a.toNat).foldlM
    (fun last (i : Nat) => do let e ← atE l ((i : Int) + 1); pure (if isConf e then ((i + 1 : Nat) : Int) else last)) 0

/-- R 163-168 `ConfOf(l, a)`: the configuration the changes among the first `a` entries make. -/
def confOf (l : List Entry) (a : Int) (initConf : Conf) : EvalM Conf := do
  if a < 0 then evalError "ConfOf: a recursive function applied outside 0..a"
  (List.range a.toNat).foldlM
    (fun c (i : Nat) => do let e ← atE l ((i : Int) + 1); if isConf e then nextConf c e.value else pure c) initConf

/-- R 171 `Cardinality(ConfsAfter(l, a))`, `ConfsAfter(l, a) == {k \in (a + 1)..Len(l) :
IsConf(l[k])}` (Go: `confsAfterCount`, which indexes `l[a]` first: out of range for `a < 0`). -/
def confsAfterCount (l : List Entry) (a : Int) : EvalM Nat :=
  if a < 0 then evalError "ConfsAfter: an index below the log"
  else pure ((l.drop a.toNat).filter isConf).length

/-- R 140 `InitConf`. -/
def State.initConf (s : State) : Conf := s.cfg.initConf

/-- R 174 `AllSwitched(i, l) == ConfsAfter(l, confAt[i]) = {}`. -/
def State.allSwitched (s : State) (i : Nat) (l : List Entry) : EvalM Bool := do
  return (← confsAfterCount l (s.confAt[i]!)) == 0

/-- R 175 `OneWaiting(i, l) == Cardinality(ConfsAfter(l, confAt[i])) <= 1`. -/
def State.oneWaiting (s : State) (i : Nat) (l : List Entry) : EvalM Bool := do
  return decide ((← confsAfterCount l (s.confAt[i]!)) ≤ 1)

/-- R 132 `LastTerm(i) == TermAt(log[i], Len(log[i]))`. -/
def State.lastTerm (s : State) (i : Nat) : Int := termAt (s.log[i]!) (s.log[i]!).length

/-- R 217-219 `VoteRequest(i, t)`. -/
def State.voteRequest (s : State) (i : Nat) (t : Int) : Fact :=
  { type := go!"vote", src := s.cfg.server[i]!, term := t, lastLogIndex := (s.log[i]!).length,
    lastLogTerm := s.lastTerm i }

/-- R 237-239 `UpToDate`, for a vote request `m`. -/
def State.upToDate (s : State) (m : Fact) (i : Nat) : Bool :=
  decide (m.lastLogTerm > s.lastTerm i) ||
    (m.lastLogTerm == s.lastTerm i && decide (m.lastLogIndex ≥ (s.log[i]!).length))

/-- R 277-280 `Granted(i)`. -/
def State.granted (s : State) (i : Nat) : SSet :=
  let me := s.cfg.server[i]!
  let out := s.cfg.server.foldl (fun out j =>
    if j != me && s.msgs.contains { type := go!"grant", src := j, dst := me, term := s.currentTerm[i]! }
    then setAdd out j else out) []
  if s.votes.contains { voter := me, term := s.currentTerm[i]!, cand := me } then setAdd out me else out

/-- R 344-347 `Acked(i, t, c)`. -/
def State.acked (s : State) (i : Nat) (t c : Int) : SSet :=
  let me := s.cfg.server[i]!
  s.cfg.server.foldl (fun out j =>
    if s.msgs.any (fun a => a.type == go!"ack" && a.src == j && a.dst == me && a.term == t && decide (a.index ≥ c))
    then setAdd out j else out) []

/-- R 366-369 `PrevOk(j, m)`. -/
def State.prevOk (s : State) (j : Nat) (m : AppendFact) : EvalM Bool := do
  if m.prevLogIndex == 0 then return true
  if m.prevLogIndex ≤ (s.log[j]!).length then
    return (← atE (s.log[j]!) m.prevLogIndex).term == m.prevLogTerm
  return false

/-- R 372-375 `HasFirst(j, m, k)`: for `q` in `1..k`, `m.prevLogIndex + q <= Len(log[j])` and the
terms agree; stops at the first `q` that fails. -/
def State.hasFirst (s : State) (j : Nat) (m : AppendFact) (k : Int) : EvalM Bool :=
  (List.range k.toNat).foldlM (fun ok (q : Nat) => do
    if !ok then return false
    let q : Int := (q : Int) + 1
    andM (pure (decide (m.prevLogIndex + q ≤ (s.log[j]!).length)))
      (do pure ((← atE (s.log[j]!) (m.prevLogIndex + q)).term == (← atE m.entries q).term))) true

/-- R 581-582 `ElectionSafety`. -/
def State.electionSafety (s : State) : Bool :=
  s.leaders.all (fun a => s.leaders.all (fun b => !(a.term == b.term && a.server != b.server)))

/-- R 585-586 `OneVotePerTerm`. -/
def State.oneVotePerTerm (s : State) : Bool :=
  s.votes.all (fun a => s.votes.all (fun b => !(a.voter == b.voter && a.term == b.term && a.cand != b.cand)))

end AntCheck
end EtcdGrove
end Perennial
