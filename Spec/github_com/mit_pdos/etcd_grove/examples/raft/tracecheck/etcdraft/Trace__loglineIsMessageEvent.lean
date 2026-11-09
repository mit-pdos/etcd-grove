/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.loglineIsMessageEvent(ts, e, i, j)`, `LoglineIsMessageEvent(e, i, j)`.
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

/-- `t.loglineIsMessageEvent(ts, e, i, j)`, at a position at least 1: `tr.isMessageEvent ts e i j`. -/
abbrev Trace.loglineIsMessageEvent.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (e : GoString) (es : String) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜strRel e es ∧ 1 ≤ ts.l⌝ }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"loglineIsMessageEvent")) (Val #g)) (Val #e)) (Val #i)) (Val #j))
  {{ RET #(tr.isMessageEvent ts es (uint.nat i) (uint.nat j)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
