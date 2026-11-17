/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.Event(l)`, `TraceLog[l].event`.
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

/-- `t.Event(l)`, at a line of the trace: a pointer to its event. -/
abbrev Trace.Event.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ ⌜1 ≤ sint.Z l ∧ sint.Z l ≤ (tr.len : Int)⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"Event")) (Val #l))
  {{ (p : Loc), RET #p; ∃ ge : G.Event, p ↦□ ge ∗ eventRO ge (tr.line (sint.nat l)).ev }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
