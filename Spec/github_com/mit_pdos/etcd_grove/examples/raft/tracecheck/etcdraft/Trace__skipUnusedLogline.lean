/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.skipUnusedLogline(ts)`, `SkipUnusedLogline`.
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

/-- `t.skipUnusedLogline(ts)`, at a position of the trace: `tr.skipUnusedLogline ts`. -/
abbrev Trace.skipUnusedLogline.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜1 ≤ ts.l ∧ ts.l ≤ tr.len⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"skipUnusedLogline")) (Val #g))
  {{ RET #(tr.skipUnusedLogline ts); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
