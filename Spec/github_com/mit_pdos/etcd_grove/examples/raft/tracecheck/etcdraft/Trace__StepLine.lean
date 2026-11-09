/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.StepLine(ts, invariants)`, the states one line
of the trace reaches from `ts` (`Tla/Check.lean`'s `StepLineRel`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StepOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section types
variable [GooseExts]
abbrev G.StepInfo := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StepInfo
end types

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `t.StepLine(ts, invariants)`, from a state of the trace specification whose search meets its
callees' premises (`Trace.StepLineOk`: every state it expands meets `Next`'s, every state it reaches
`Violated`'s when checked) and where the Lean search does not fail (no `StepLineRel` to an
`EvalError`: the Go panics with an `EvalError` where TLC fails): the states and the step information
`StepLineRel` relates `ts` to (the Go's `Bad` unconstrained), the states fresh. Partial correctness: a
search that never ends returns nothing. -/
abbrev Trace.StepLine.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (invariants : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜tr.StepLineOk ts invariants ∧ ∀ e, ¬ tr.StepLineRel ts invariants (.error e)⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"StepLine")) (Val #g)) (Val #invariants))
  {{ (out : GoSlice) (gi : G.StepInfo), RET (PairV #out #gi);
      ∃ (tss : List TState) (info : StepInfo),
        ⌜tr.StepLineRel ts invariants (.ok (tss, info)) ∧ gi.Branched' = info.branched ∧
          strRel gi.Violation' (info.violation.getD "")⌝ ∗ tstatesOut out tss }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
