/-
Lean-first (no Rocq counterpart). Draft (2026-11-08), layer C of `notes/trace-validation-plan.md`.

`CheckTrace(t, invariants)` (`examples/raft/tracecheck/etcdraft/check.go`): TLC's check of the
trace `t` against `Traceetcdraft.tla` (its breadth-first search, line by line, deduplicated by the
view `<<vars, l>>`, the invariants checked at every state reached when `invariants`; an evaluation
TLC would fail is a failure). Its spec: what it returns is the result the Lean transcription's
`CheckTraceRel` (`Tla/Check.lean`, the search as a relation, without fuel: Q7, the user's choice
2026-11-08) relates the trace to, on the fields it records (`resultRel`); so `Result.TLCOK()` holds
only of a trace the relation accepts, and with `NewTrace`'s spec, `TraceAccepts evs false false` is
`Main`'s check.
Partial correctness: a search that never ends returns nothing.
The trace is read, not written (`traceRO`, which carries what `NewTrace` establishes: the Go's search
relies on that, review round 1 of layer C, F1).
Its premise `Trace.CheckTraceOk` (`CheckOk.lean`; Q10 of the plan, 2026-11-09): the search meets its
callees' premises, which are stated where the Lean transcription evaluates, on the workload's kinds of
lines and on states far from overflow. It has three parts: the lines outside the bootstrap in scope
(no `ChangeConf`, restart or snapshot); the lines' configuration lists (each event's incoming `conf`
list, a configuration change's `newconf`) shorter than `numBound` (`Trace.ConfsBounded`), which
`Event.Bounded` does not bound and `NewTrace` does not check (with `Trace.Valid` and the lines in scope,
every state reachable from `TraceInit` is then bounded: `Trace.Valid.reach_searchOk`); and, a premise on
the search itself, that it raises no evaluation error (where TLC fails, the Go panics with an `EvalError`
and recovers, returning a failing `Result` whose `Branched` may differ from the relation's, which its
callees' triples do not describe): the spec covers only such runs. So the spec says nothing of the
traces outside that class. `Main` is to discharge it of the trace raft produces with
`Trace.RunRel.checkTraceOk`, from the lines in scope, raft's configurations of three ids
(`Trace.confsBounded_of_newTrace`) and layer B's run.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- See the file header. -/
abbrev CheckTrace.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (invariants : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ ⌜tr.CheckTraceOk invariants⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckTrace))
      (Val #t)) (Val #invariants))
  {{ (r : G.Result), RET #r; ∃ lr, ⌜CheckTraceRel tr invariants lr ∧ resultRel r lr⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
