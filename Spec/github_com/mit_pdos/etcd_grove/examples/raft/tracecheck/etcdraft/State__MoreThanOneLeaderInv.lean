/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `State.MoreThanOneLeaderInv()`:
`MoreThanOneLeaderInv` (`State.moreThanOneLeaderInv`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

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

/-- `s.MoreThanOneLeaderInv()`: whether no two servers lead in one term. -/
abbrev State.MoreThanOneLeaderInv.spec : Prop :=
  ∀ (p : Loc) (st : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"MoreThanOneLeaderInv")) (Val #()))
  {{ RET #(st.moreThanOneLeaderInv); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
