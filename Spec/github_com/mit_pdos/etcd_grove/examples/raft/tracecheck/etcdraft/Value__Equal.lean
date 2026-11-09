/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `v.Equal(w)`: `v = w`.
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

/-- `v.Equal(w)`: `v = w` (the values' relation is canonical, so Go's field-wise equality is the
Lean's). -/
abbrev Value.Equal.spec : Prop :=
  ∀ (v : G.Value) (a : Value) (w : G.Value) (b : Value),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      valueRO v a ∗ valueRO w b }}
    (App (Val (v @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Value.ty @!! go!"Equal")) (Val #w))
  {{ RET #(decide (a = b)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
