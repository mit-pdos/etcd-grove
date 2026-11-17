/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `oneLessMessage(s, s2, m)`, `OneLessMessage(msg)`.
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

/-- `oneLessMessage(s, s2, m)`: `oneLessMessage s s2 m`. -/
abbrev oneLessMessage.spec : Prop :=
  ∀ (p : Loc) (s : State) (p2 : Loc) (s2 : State) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p s ∗ stateRO p2 s2 ∗ msgRO q m }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.oneLessMessage))
      (Val #p)) (Val #p2)) (Val #q))
  {{ RET #(oneLessMessage s s2 m); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
