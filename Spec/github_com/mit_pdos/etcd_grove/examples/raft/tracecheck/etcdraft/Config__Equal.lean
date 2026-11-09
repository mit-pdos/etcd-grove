/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `c.Equal(d)`: `c = d`.
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

/-- `c.Equal(d)`: `c = d`. -/
abbrev Config.Equal.spec : Prop :=
  ∀ (g : G.Config) (c : Config) (h : G.Config) (d : Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      configRO g c ∗ configRO h d }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config.ty @!! go!"Equal")) (Val #h))
  {{ RET #(decide (c = d)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
