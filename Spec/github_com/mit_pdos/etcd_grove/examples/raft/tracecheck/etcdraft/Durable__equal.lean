/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `d.equal(e)`: `d = e`.
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

/-- `d.equal(e)`: `d = e`. -/
abbrev Durable.equal.spec : Prop :=
  ∀ (g : G.Durable) (d : Durable) (h : G.Durable) (e : Durable),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      durableRO g d ∗ durableRO h e }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Durable.ty @!! go!"equal")) (Val #h))
  {{ RET #(decide (d = e)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
