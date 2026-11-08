/-
Lean-first (no Rocq counterpart).

# raft's TLA+ specification in Lean: the invariants (2026-11-08)

The correctness invariants of `etcdraft.tla`, mirroring the Go transcription's `invariants.go`;
`invariants` lists those `Traceetcdraft.cfg` checks, in its order. Each is `EvalM Bool`: `Committed`
and `LeaderCompletenessInv` fail where TLC fails evaluating them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Spec

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-- `Committed(i) == SubSeq(log[i],1,commitIndex[i])`. -/
def State.committed (st : State) (i : ID) : EvalM (List Entry) :=
  subSeqM (st.s i).log 1 (st.s i).commitIndex

/-- `MessageTermsLtCurrentTerm(m)` (no configuration checks it). -/
def State.messageTermsLtCurrentTerm (st : State) (m : Msg) : Bool :=
  st.server.contains m.source && m.term ≤ (st.s m.source).currentTerm

/-- `LogInv`. -/
def State.logInv (st : State) : EvalM Bool :=
  st.server.allM (fun i => st.server.allM (fun j => do
    let ci ← st.committed i
    let cj ← st.committed j
    return isPrefix ci cj || isPrefix cj ci))

/-- `MoreThanOneLeaderInv`. -/
def State.moreThanOneLeaderInv (st : State) : Bool :=
  st.server.all (fun i => st.server.all (fun j =>
    !((st.s i).currentTerm == (st.s j).currentTerm && (st.s i).state == leader && (st.s j).state == leader) ||
      i == j))

/-- `MaxOrZero({n \in DOMAIN xlog : xlog[n].term = t})`. -/
def maxIndexOfTerm (xlog : List Entry) (t : Int) : Nat :=
  (List.range xlog.length).foldl
    (fun (acc : Nat) n => if ((xlog[n]?).map Entry.term) == some t then n + 1 else acc) 0

/-- `ElectionSafetyInv`. -/
def State.electionSafetyInv (st : State) : Bool :=
  st.server.all (fun i =>
    (st.s i).state != leader ||
      st.server.all (fun j =>
        maxIndexOfTerm (st.s i).log (st.s i).currentTerm ≥ maxIndexOfTerm (st.s j).log (st.s i).currentTerm))

/-- `LogMatchingInv`. -/
def State.logMatchingInv (st : State) : Bool :=
  st.server.all (fun i => st.server.all (fun j =>
    let li := (st.s i).log
    let lj := (st.s j).log
    (List.range (min li.length lj.length)).all (fun n =>
      -- n is TLA+'s n - 1
      ((li[n]?).map Entry.term) != ((lj[n]?).map Entry.term) || li.take (n + 1) == lj.take (n + 1))))

/-- `QuorumLogInv`: every quorum of `GetConfig(i)` has a server whose log extends `Committed(i)`;
equivalently, the servers of the configuration whose log does not are no quorum. -/
def State.quorumLogInv (st : State) : EvalM Bool :=
  st.server.allM (fun i => do
    let cfg := st.getConfig i
    let c ← st.committed i
    let without := cfg.filter (fun j => !st.server.contains j || !isPrefix c (st.s j).log)
    return !isQuorum without cfg)

/-- `MoreUpToDateCorrectInv`, which is false (`issues/raft-tla-more-up-to-date-cut-batches.md`) and
not checked (`etc/tla-fixes` 0009). -/
def State.moreUpToDateCorrectInv (st : State) : EvalM Bool :=
  st.server.allM (fun i => st.server.allM (fun j => do
    let li := (st.s i).log
    let lj := (st.s j).log
    if lastTerm li > lastTerm lj || (lastTerm li == lastTerm lj && li.length ≥ lj.length) then
      return isPrefix (← st.committed j) li
    return true))

/-- `LeaderCompletenessInv`, repaired: the leader's term also at least the committing server's
(`currentTerm[l] >= currentTerm[i]`; upstream's guard alone fails with a stale leader:
`issues/raft-tla-leader-completeness-stale-leader.md`, `notes/trace-validation-plan.md`, Q4 (b)).
`log[l][idx]` past a leader's log fails, as TLC does. -/
def State.leaderCompletenessInv (st : State) : EvalM Bool := do
  let leaders := st.currentLeaders
  st.server.allM (fun i => do
    let c ← st.committed i
    (List.range c.length).allM (fun idx0 => do
      -- idx0 is TLA+'s idx - 1
      let entry := ((st.s i).log[idx0]?).getD default
      leaders.allM (fun l => do
        let vl := st.s l
        if vl.currentTerm > entry.term && vl.currentTerm ≥ (st.s i).currentTerm then
          let some e := vl.log[idx0]?
            | throw { what := "LeaderCompletenessInv: log[l][idx] past the log's end (l, idx, length)",
                      a := l, b := idx0 + 1, c := vl.log.length }
          return e == entry
        else return true)))

/-- `CommittedIsDurableInv`. -/
def State.committedIsDurableInv (st : State) : Bool :=
  st.server.all (fun i => (st.s i).state != leader || (st.s i).commitIndex ≤ (st.s i).durable.log.length)

/-- The invariants `Traceetcdraft.cfg` checks, in its order, with their names. -/
def invariants : List (String × (State → EvalM Bool)) :=
  [ ("LogInv", State.logInv),
    ("MoreThanOneLeaderInv", fun st => pure st.moreThanOneLeaderInv),
    ("ElectionSafetyInv", fun st => pure st.electionSafetyInv),
    ("LogMatchingInv", fun st => pure st.logMatchingInv),
    ("QuorumLogInv", State.quorumLogInv),
    ("LeaderCompletenessInv", State.leaderCompletenessInv),
    ("CommittedIsDurableInv", fun st => pure st.committedIsDurableInv) ]

/-- The name of the first invariant `st` violates, or `none` (Go: `State.Violated`). -/
def State.violated (st : State) : EvalM (Option String) :=
  invariants.foldlM (fun acc inv => do
    match acc with
    | some v => return some v
    | none => return if (← inv.2 st) then none else some inv.1) none

end Etcdraft
end EtcdGrove
end Perennial
