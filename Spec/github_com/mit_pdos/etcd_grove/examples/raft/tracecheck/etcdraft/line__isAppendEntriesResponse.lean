/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `ln.isAppendEntriesResponse(m)`, `LoglineIsAppendEntriesResponse(m)`.
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

/-- `ln.isAppendEntriesResponse(m)`: `x.isAppendEntriesResponse m`. -/
abbrev line.isAppendEntriesResponse.spec : Prop :=
  ∀ (q : Loc) (x : Line) (p : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      linePtrRO q x ∗ msgRO p m }}
    (App (Val (q @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line.ty
      @!! go!"isAppendEntriesResponse")) (Val #p))
  {{ RET #(x.isAppendEntriesResponse m); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
