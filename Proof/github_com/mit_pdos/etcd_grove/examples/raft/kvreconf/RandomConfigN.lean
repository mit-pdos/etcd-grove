/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/RandomConfigN.lean`. Lean-first
(no Rocq counterpart; 2026-11-16, kvraftN): `RandomConfig.lean`'s, from `RandomOptionsN`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.RandomConfigN
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.RandomOptionsN
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

theorem RandomConfigN.wp_proof (wp_RandomOptionsN : RandomOptionsN.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG)) :
    RandomConfigN.spec (GF := GF) (hG := hG) := by
  intro k Hk1 Hk
  wp_start as #Hpkg
  try wp_auto
  wp_apply (wp_RandomOptionsN k Hk1 Hk) as %o %Ho
  wp_apply wp_below as %r %Hr
  try wp_auto
  have h := Hr.2 (by decide)
  iapply HΦ
  ipureintro
  refine ⟨Ho.1, Ho.2, rfl, rfl, ?_, ?_⟩ <;> word

end proof

end raft_kvreconf
end EtcdGrove
end Perennial
