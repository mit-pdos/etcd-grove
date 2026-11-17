/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.loglineIsNodeEvent(ts, e, i)`, `LoglineIsNodeEvent(e, i)`.
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

/-- `t.loglineIsNodeEvent(ts, e, i)`, at a position at least 1: `tr.isNodeEvent ts e i`. -/
abbrev Trace.loglineIsNodeEvent.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (e : GoString) (es : String) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜strRel e es ∧ 1 ≤ ts.l⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"loglineIsNodeEvent")) (Val #g)) (Val #e)) (Val #i))
  {{ RET #(tr.isNodeEvent ts es (uint.nat i)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
