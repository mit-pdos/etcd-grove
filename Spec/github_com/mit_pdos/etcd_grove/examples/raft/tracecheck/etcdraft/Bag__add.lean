/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.add(m, n)`: `b` with `n` more of `m` (`Bag.add`).
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

/-- `b.add(m, n)`: a fresh bag, `b` with `n` more of `m`. Premises: `b`'s messages distinct (the
Go adds to the first item holding `m`, the Lean to every one; a bag's messages are distinct, as
`Bag` says, and `add` keeps them so), and the new count within the Go's `int`. -/
abbrev Bag.add.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (p : Loc) (m : Msg) (nw : w64) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ msgRO p m ∗
      ⌜(b.map Prod.fst).Nodup ∧ sint.Z nw = (n : Int) ∧ (b.count m : Int) + n < 2 ^ 63⌝ }}
    (App (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"add")) (Val #p)) (Val #nw))
  {{ (g' : G.Bag), RET #g'; bagRO g' (b.add m n) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
