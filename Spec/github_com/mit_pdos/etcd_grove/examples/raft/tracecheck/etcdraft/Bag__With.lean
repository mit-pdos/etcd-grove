/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.With(m)`: `WithMessage(m, b)` (`Bag.with`).
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

/-- `b.With(m)`: `b` with one more `m`. Premises as `add`'s. -/
abbrev Bag.With.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (p : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ msgRO p m ∗ ⌜(b.map Prod.fst).Nodup ∧ (b.count m : Int) + 1 < 2 ^ 63⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"With")) (Val #p))
  {{ (g' : G.Bag), RET #g'; bagRO g' (b.with m) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
