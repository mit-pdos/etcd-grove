/-
Lean-first (no Rocq counterpart).

# raft's TLA+ trace validation in Lean: the check (2026-11-08)

`checkTrace`, mirroring the Go transcription's `CheckTrace` (`check.go`): TLC's breadth-first
search, line by line, of the states `TraceNext` reaches, deduplicated by TLC's view
`<<vars, l>>`, checking every state reached against the invariants. `Result.tlcOK` is TLC's
verdict (matched, the search never branched, no invariant violated, no evaluation failed): what
`Main` panics without, and the statement's meaning (`TraceAccepts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Tla.Trace

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-- The outcome of checking a trace (Go: `Result`, without the debugging fields). -/
structure Result where
  /-- Some behavior steps through every line, no state reached violates an invariant, no
  evaluation fails. -/
  ok : Bool := false
  /-- The first line at which some state had more than one new successor, 0 if none. -/
  branched : Nat := 0
  /-- The first line no state could step through (when not ok for another reason). -/
  line : Nat := 0
  /-- The first invariant violated, at `violLine`. -/
  violation : Option String := none
  violLine : Nat := 0
  /-- Where TLC would stop with an error, at `errLine`. -/
  evalError : Option EvalError := none
  errLine : Nat := 0
  deriving Repr, Inhabited

/-- TLC's verdict: ok, and the search never branched (Go: `Result.TLCOK`). -/
def Result.tlcOK (r : Result) : Bool := r.ok && r.branched == 0

/-- One line of the search: the states at the next line, deduplicated, and the line's branching
and violation (Go: `CheckTrace`'s loop body). -/
def Trace.checkLine (t : Trace) (invariants : Bool) (frontier : List TState) :
    EvalM (List TState × StepInfo) :=
  frontier.foldlM (fun (acc : List TState × StepInfo) ts => do
    let (next, info) := acc
    if info.violation.isSome then return acc
    let (succ, i2) ← t.stepLine ts invariants
    let next := succ.foldl (fun nx s2 => if memEq nx s2 then nx else nx ++ [s2]) next
    return (next, { branched := info.branched || i2.branched, violation := i2.violation }))
    ([], {})

/-- The search from line `l` on, `frontier` the states at line `l` (Go: `CheckTrace`'s loop). -/
def Trace.checkFrom (t : Trace) (invariants : Bool) : Nat → Nat → List TState → Result → Result
  | 0, _, _, r => { r with ok := true }
  | fuel + 1, l, frontier, r =>
    match t.checkLine invariants frontier with
    | .error e => { evalError := some e, errLine := l, branched := r.branched }
    | .ok (next, info) =>
      -- (as the Go's `CheckTrace`: a state's branching first, then a violation returns, and only
      -- then the line's own count of next states)
      let r := if info.branched && r.branched == 0 then { r with branched := l } else r
      match info.violation with
      | some v => { violation := some v, violLine := l, branched := r.branched }
      | none =>
        if next.isEmpty then { r with line := l }
        else
          let r := if next.length > 1 && r.branched == 0 then { r with branched := l } else r
          t.checkFrom invariants fuel (l + 1) next r

/-- `checkTrace t invariants` (Go: `CheckTrace`). -/
def checkTrace (t : Trace) (invariants : Bool) : Result :=
  let init := t.initState
  if invariants then
    match init.s.violated with
    | .error e => { evalError := some e, errLine := 0 }
    | .ok (some v) => { violation := some v, violLine := 0 }
    | .ok none => t.checkFrom invariants t.len 1 [init] {}
  else t.checkFrom invariants t.len 1 [init] {}

/-- `TraceAccepts events`: the trace of `events` is one the specification reads and TLC would
accept (what `Main` checks; the corollary's statement). -/
def traceAccepts (events : List Event) : Bool :=
  match newTrace events with
  | .error _ => false
  | .ok t => (checkTrace t true).tlcOK

/-! ## The check as a relation (no fuel)

`checkTrace` above runs, for tests (`#eval` against TLC and the Go checker), but its per-line loop
(`stepLoop`) needs fuel, which Lean's termination asks for and the Go's loop does not have; where
the fuel ran out it would stop early. The statement is written instead with the relations below:
the same search, a constructor per outcome of a round of the loop, so a run of any length is a
derivation and none is cut short (`notes/trace-validation-plan.md`, Q7, the user's choice
2026-11-08). The search is deterministic, so each relation relates an input to at most one result;
a loop that never ends relates it to none (the Go checker then never returns: the closed theorem,
which is about panics, says nothing more of such a run). -/

/-- `stepLine`'s loop from `frontier` and `(out, visited, info)`, as a relation: one round at a
time until the frontier is empty, a round fails, or a round finds a violation. -/
inductive Trace.StepLoop (t : Trace) (l0 : Nat) (invariants : Bool) :
    List TState → List TState × List TState × StepInfo → EvalM (List TState × StepInfo) → Prop
  | done (st : List TState × List TState × StepInfo) :
      Trace.StepLoop t l0 invariants [] st (.ok (st.1, st.2.2))
  | error (frontier : List TState) (st : List TState × List TState × StepInfo) (e : EvalError) :
      frontier ≠ [] → t.stepRound l0 invariants frontier st = .error e →
      Trace.StepLoop t l0 invariants frontier st (.error e)
  | violation (frontier : List TState) (st : List TState × List TState × StepInfo)
      (out visited next : List TState) (info : StepInfo) :
      frontier ≠ [] → t.stepRound l0 invariants frontier st = .ok (out, visited, next, info) →
      info.violation.isSome →
      Trace.StepLoop t l0 invariants frontier st (.ok (out, info))
  | round (frontier : List TState) (st : List TState × List TState × StepInfo)
      (out visited next : List TState) (info : StepInfo) (r : EvalM (List TState × StepInfo)) :
      frontier ≠ [] → t.stepRound l0 invariants frontier st = .ok (out, visited, next, info) →
      info.violation.isNone →
      Trace.StepLoop t l0 invariants next (out, visited, info) r →
      Trace.StepLoop t l0 invariants frontier st r

/-- `stepLine`, as a relation (Go: `Trace.StepLine`). -/
def Trace.StepLineRel (t : Trace) (ts : TState) (invariants : Bool) (r : EvalM (List TState × StepInfo)) : Prop :=
  t.StepLoop ts.l invariants [ts] ([], [ts], {}) r

/-- `checkLine`, as a relation: its fold over the frontier, each element's `stepLine` related. -/
inductive Trace.CheckLineRel (t : Trace) (invariants : Bool) :
    List TState → List TState × StepInfo → EvalM (List TState × StepInfo) → Prop
  | nil (acc : List TState × StepInfo) : Trace.CheckLineRel t invariants [] acc (.ok acc)
  | skip (ts : TState) (rest : List TState) (acc : List TState × StepInfo) (r : EvalM (List TState × StepInfo)) :
      acc.2.violation.isSome → Trace.CheckLineRel t invariants rest acc r →
      Trace.CheckLineRel t invariants (ts :: rest) acc r
  | error (ts : TState) (rest : List TState) (acc : List TState × StepInfo) (e : EvalError) :
      acc.2.violation.isNone → t.StepLineRel ts invariants (.error e) →
      Trace.CheckLineRel t invariants (ts :: rest) acc (.error e)
  | step (ts : TState) (rest : List TState) (acc : List TState × StepInfo) (succ : List TState) (i2 : StepInfo)
      (r : EvalM (List TState × StepInfo)) :
      acc.2.violation.isNone → t.StepLineRel ts invariants (.ok (succ, i2)) →
      Trace.CheckLineRel t invariants rest
        (succ.foldl (fun nx s2 => if memEq nx s2 then nx else nx ++ [s2]) acc.1,
         { branched := acc.2.branched || i2.branched, violation := i2.violation }) r →
      Trace.CheckLineRel t invariants (ts :: rest) acc r

/-- `checkFrom`, as a relation (the line count `n`, `Len(TraceLog)` at the start, is exact: one line
per step). -/
inductive Trace.CheckFromRel (t : Trace) (invariants : Bool) : Nat → Nat → List TState → Result → Result → Prop
  | stop (l : Nat) (frontier : List TState) (r : Result) :
      Trace.CheckFromRel t invariants 0 l frontier r { r with ok := true }
  | error (n l : Nat) (frontier : List TState) (r : Result) (e : EvalError) :
      t.CheckLineRel invariants frontier ([], {}) (.error e) →
      Trace.CheckFromRel t invariants (n + 1) l frontier r { evalError := some e, errLine := l, branched := r.branched }
  | violation (n l : Nat) (frontier : List TState) (r : Result) (next : List TState) (info : StepInfo) (v : String) :
      t.CheckLineRel invariants frontier ([], {}) (.ok (next, info)) → info.violation = some v →
      Trace.CheckFromRel t invariants (n + 1) l frontier r
        { violation := some v, violLine := l,
          branched := (if info.branched && r.branched == 0 then { r with branched := l } else r).branched }
  | unmatched (n l : Nat) (frontier : List TState) (r : Result) (info : StepInfo) :
      t.CheckLineRel invariants frontier ([], {}) (.ok ([], info)) → info.violation = none →
      Trace.CheckFromRel t invariants (n + 1) l frontier r
        { (if info.branched && r.branched == 0 then { r with branched := l } else r) with line := l }
  | step (n l : Nat) (frontier : List TState) (r : Result) (next : List TState) (info : StepInfo) (r' : Result) :
      t.CheckLineRel invariants frontier ([], {}) (.ok (next, info)) → info.violation = none → next ≠ [] →
      Trace.CheckFromRel t invariants n (l + 1) next
        (let r := if info.branched && r.branched == 0 then { r with branched := l } else r
         if next.length > 1 && r.branched == 0 then { r with branched := l } else r) r' →
      Trace.CheckFromRel t invariants (n + 1) l frontier r r'

/-- `checkTrace`, as a relation (Go: `CheckTrace`). -/
def CheckTraceRel (t : Trace) (invariants : Bool) (res : Result) : Prop :=
  let init := t.initState
  if invariants then
    match init.s.violated with
    | .error e => res = { evalError := some e, errLine := 0 }
    | .ok (some v) => res = { violation := some v, violLine := 0 }
    | .ok none => t.CheckFromRel invariants t.len 1 [init] {} res
  else t.CheckFromRel invariants t.len 1 [init] {} res

/-- `TraceAccepts events`: the trace of `events` is one the specification reads and TLC would
accept, for raft's `PreVote` and `CheckQuorum` (the corollary's statement; what `Main` checks). -/
def TraceAccepts (events : List Event) (preVote checkQuorum : Bool) : Prop :=
  ∃ t, newTraceWith events preVote checkQuorum = .ok t ∧ ∃ res, CheckTraceRel t true res ∧ res.tlcOK = true

end Etcdraft
end EtcdGrove
end Perennial
