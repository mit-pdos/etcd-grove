/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.sub(m, n)`: `b` with `n` fewer of `m` (`Bag.sub`).
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

/-- `b.sub(m, n)`: `b` with `n` fewer of `m`, none below zero (a fresh bag, or `b` itself when `m`
is not in it). Premise: `b`'s messages distinct (the Go subtracts from the first item holding `m`,
the Lean from every one). -/
abbrev Bag.sub.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (p : Loc) (m : Msg) (nw : w64) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ msgRO p m ∗ ⌜(b.map Prod.fst).Nodup ∧ sint.Z nw = (n : Int)⌝ }}
    (App (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"sub")) (Val #p)) (Val #nw))
  {{ (g' : G.Bag), RET #g'; bagRO g' (b.sub m n) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
