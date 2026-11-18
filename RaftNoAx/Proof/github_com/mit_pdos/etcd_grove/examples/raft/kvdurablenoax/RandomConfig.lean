-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/RandomConfig.lean` (etc/copy-part.py; rerun it, do not edit).
/-
kvreconf's proof (the same Go text), ported.
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/RandomConfig.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.RandomConfig
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.RandomOptions
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]

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
  refine ⟨Ho.1, Ho.2, rfl, rfl, ?_, ?_⟩ <;> word

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
