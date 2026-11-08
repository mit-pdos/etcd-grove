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
      let r := if (info.branched || next.length > 1) && r.branched == 0 then { r with branched := l } else r
      match info.violation with
      | some v => { violation := some v, violLine := l, branched := r.branched }
      | none =>
        if next.isEmpty then { r with line := l }
        else t.checkFrom invariants fuel (l + 1) next r

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

end Etcdraft
end EtcdGrove
end Perennial
