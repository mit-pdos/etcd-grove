/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.Count(m)` (`Bag.count`).
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

/-- `b.Count(m)`: `m`'s count in `b`. -/
abbrev Bag.Count.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (p : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ msgRO p m }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"Count")) (Val #p))
  {{ (c : w64), RET #c; ⌜sint.Z c = (b.count m : Int)⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
