/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.validatePostStates(ts, s, i)`, `ValidatePostStates(i)` of the successor `s`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

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

/-- `t.validatePostStates(ts, s, i)`, at a position of the trace: `tr.validatePostStates ts st i`. -/
abbrev Trace.validatePostStates.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ stateRO p st ∗ ⌜1 ≤ ts.l ∧ ts.l ≤ tr.len⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"validatePostStates")) (Val #g)) (Val #p)) (Val #i))
  {{ RET #(tr.validatePostStates ts st (uint.nat i)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
