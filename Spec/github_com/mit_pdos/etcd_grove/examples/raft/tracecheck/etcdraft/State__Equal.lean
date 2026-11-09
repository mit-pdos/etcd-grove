/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Equal(t)`: `vars = vars` (`State.eq`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

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

/-- `s.Equal(t)`: TLC's view `vars` of the two states equal (`State.eq`). -/
abbrev State.Equal.spec : Prop :=
  ∀ (p : Loc) (s : State) (q : Loc) (t : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p s ∗ stateRO q t }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Equal")) (Val #q))
  {{ RET #(s.eq t); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
