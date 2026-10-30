/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/RandomConfig.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.RandomConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.RandomOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem RandomConfig.wp_proof (wp_RandomOptions : RandomOptions.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG)) :
    RandomConfig.spec (GF := GF) (hG := hG) := by
  wp_start as #Hpkg
  try wp_auto
  wp_apply wp_RandomOptions as %o %Ho
  wp_apply wp_below as %r %Hr
  try wp_auto
  have h := Hr.2 (by decide)
  iapply HΦ
  ipureintro
  refine ⟨Ho, rfl, rfl, ?_, ?_⟩ <;> word

end proof

end kvreconf
end EtcdGrove
end Perennial
