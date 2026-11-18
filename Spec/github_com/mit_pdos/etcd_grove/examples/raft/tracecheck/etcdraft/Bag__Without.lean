/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.Without(m)`: `WithoutMessage(m, b)` (`Bag.without`).
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

/-- `b.Without(m)`: `b` with one fewer `m` (`b` itself when `m` is not in it). Premise as `sub`'s. -/
abbrev Bag.Without.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (p : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ msgRO p m ∗ ⌜(b.map Prod.fst).Nodup⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"Without")) (Val #p))
  {{ (g' : G.Bag), RET #g'; bagRO g' (b.without m) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
