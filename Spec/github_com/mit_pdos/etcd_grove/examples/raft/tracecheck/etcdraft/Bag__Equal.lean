/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.Equal(c)`: `b = c` as bags (`Bag.eq`).
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

/-- `b.Equal(c)`: `Bag.eq b c`. -/
abbrev Bag.Equal.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (h : G.Bag) (c : Bag),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ bagRO h c }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"Equal")) (Val #h))
  {{ RET #(b.eq c); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
