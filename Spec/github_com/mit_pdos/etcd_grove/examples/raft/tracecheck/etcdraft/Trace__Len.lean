/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.Len()`, `Len(TraceLog)`.
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

/-- `t.Len()`: the trace's number of lines. -/
abbrev Trace.Len.spec : Prop :=
  ∀ (t : Loc) (tr : Trace),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"Len")) (Val #()))
  {{ (n : w64), RET #n; ⌜sint.Z n = (tr.len : Int)⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
