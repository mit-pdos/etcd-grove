/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.nonReceive(ts)`, `TraceNextNonReceiveActions`
without its `StepToNextTrace`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StepOk

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

/-- `t.nonReceive(ts)`, at a line of the trace of a kind the workload logs (`Line.InScope`), of a state
over the trace's servers meeting the actions' premises (`State.ActOk`), where the Lean evaluates
(`= .ok sts`: the Go panics with an `EvalError` where TLC fails): the successors' variables `sts`,
fresh. -/
abbrev Trace.nonReceive.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (sts : List State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ ts.l ≤ tr.len ∧ ts.s.server = tr.server ∧ ts.s.ActOk ∧ (tr.line ts.l).InScope ∧
        tr.nonReceive ts = .ok sts⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"nonReceive")) (Val #g))
  {{ (out : GoSlice), RET #out; statesOut out sts }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
