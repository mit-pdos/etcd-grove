/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.Next(ts)`, `TraceNext`.
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

/-- `t.Next(ts)`, of a state of the trace specification meeting the actions' premises
(`TState.NextOk`: a position in the trace, the trace's servers, the bounds, the bags, a line in scope
where it is not a bootstrap line), where the Lean evaluates (`= .ok tss`: the Go panics with an
`EvalError` where TLC fails): `tss`, fresh. -/
abbrev Trace.Next.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (tss : List TState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜ts.NextOk tr ∧ tr.next ts = .ok tss⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"Next")) (Val #g))
  {{ (out : GoSlice), RET #out; tstatesOut out tss }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
