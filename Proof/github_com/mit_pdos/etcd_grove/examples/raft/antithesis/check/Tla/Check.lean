/-
Lean-first (no Rocq counterpart).

# Antithesis's TLA+ model of raft in Lean: the check (#33 S3b)

`run`, mirroring the Go transcription's `Run` (`check.go`): the binding's one state, `GC` steps
taken whenever due, then the next event (B 775 `Next0 == (GC \/ Step) /\ UNCHANGED read`, `Step`
requiring `~GCDue`: at most one is enabled, and each determines its successor, so TLC's frontier
holds at most one state per event: `notes/antithesis-check-design.md` §3), the invariants of
`EtcdBinding*.cfg` checked on every new state. `Accepts cfg evs` is TLC's `ACCEPTED`: what `Main`
panics without.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Binding

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

/-- The kind of a verdict (Go: `Kind`), as streamcheck.py prints it. `error` is `Check`'s only
(the Go `Run` panics where this transcription is an `EvalM` error). -/
inductive Kind where
  | accepted | rejected | violated | error
  deriving DecidableEq, Repr, Inhabited

/-- The outcome of checking a stream (Go: `Verdict`, without `Err`, which `Run` never sets): `k`
the number of events for `accepted`, the event's index (from 1) otherwise; `names` the invariants
a `violated` state breaks. -/
structure Verdict where
  kind : Kind := .accepted
  k : Int := 0
  names : List Str := []
  deriving DecidableEq, Repr, Inhabited

/-- The invariants of `EtcdBinding*.cfg` (`ElectionSafety`, `OneVotePerTerm`, `Safe`; B 782
`Safe == viol = {}`) that `s` breaks, as TLC reports them: the first that fails, `[]` for none
(Go: `violated`). -/
def violated (s : State) : List Str :=
  if !s.electionSafety then [go!"ElectionSafety"]
  else if !s.oneVotePerTerm then [go!"OneVotePerTerm"]
  else s.viol

/-- The checker between events (Go: `Checker`). -/
structure Checker where
  state : State
  done : Bool := false
  verdict : Verdict := {}
  deriving DecidableEq, Repr, Inhabited

/-- `GC` steps while due, each new state checked against the invariants at the last event taken
(`s.i - 1`); `fuel` bounds the steps (Go: `Next`'s `for s.GCDue()` loop, which needs none). A due
`GC` removes something (`Garbage` or `OldVotes` holds `GCBatch` records of `msgs`/`votes`, or
`StaleLed` a term of `ledLog`), so `gcFuel` steps always suffice. -/
def gcLoop : Nat → State → EvalM (State × Option Verdict)
  | 0, _ => evalError "GC: out of fuel"
  | fuel + 1, s => do
    if !(← s.gcDue) then return (s, none)
    let s ← s.gc
    let v := violated s
    if v != [] then return (s, some { kind := .violated, k := s.i - 1, names := v })
    gcLoop fuel s

/-- Enough fuel for `gcLoop` from `s`. -/
def gcFuel (s : State) : Nat := s.msgs.length + s.votes.length + s.ledLog.length + 1

/-- Takes the next event (Go: `Checker.Next`); after a verdict, does nothing. -/
def Checker.next (c : Checker) (ev : Event) : EvalM Checker := do
  if c.done then return c
  let (s, v) ← gcLoop (gcFuel c.state) c.state
  if let some v := v then return { state := s, done := true, verdict := v }
  match ← s.step ev with
  | none => return { state := s, done := true, verdict := { kind := .rejected, k := s.i } }
  | some ns =>
    let v := violated ns
    if v != [] then return { state := ns, done := true, verdict := { kind := .violated, k := s.i, names := v } }
    return { c with state := ns }

/-- The verdict once the stream has ended (Go: `Checker.End`). -/
def Checker.finish (c : Checker) : Verdict :=
  if c.done then c.verdict else { kind := .accepted, k := c.state.i - 1 }

/-- The check of a whole stream (Go: `Run`): an error where TLC would stop with one. -/
def run (cfg : Config) (evs : List Event) : EvalM Verdict := do
  let c : Checker := { state := ← init0 cfg }
  let c ← evs.foldlM (fun c ev => c.next ev) c
  return c.finish

/-- TLC accepts the stream (`ACCEPTED n`): the binding takes every event, no state reached breaks
an invariant, no evaluation fails. -/
def Accepts (cfg : Config) (evs : List Event) : Prop :=
  ∃ v, run cfg evs = .ok v ∧ v.kind = .accepted

/-- `Accepts` as a computation, for `decide`/`#eval` on streams. -/
def accepts (cfg : Config) (evs : List Event) : Bool :=
  match run cfg evs with
  | .ok v => v.kind == .accepted
  | .error _ => false

theorem accepts_iff (cfg : Config) (evs : List Event) : accepts cfg evs = true ↔ Accepts cfg evs := by
  unfold accepts Accepts
  cases run cfg evs <;> simp

instance (cfg : Config) (evs : List Event) : Decidable (Accepts cfg evs) :=
  decidable_of_iff _ (accepts_iff cfg evs)

end AntCheck
end EtcdGrove
end Perennial
