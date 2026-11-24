/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/ValidCluster.lean`: `ValidAddrs`, then the conditions on raft's limits.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ValidCluster
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ValidAddrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

private theorem wand_bool_congr (P : IProp GF) (Φ : val → IProp GF) (b1 b2 : Bool) (h : b1 = b2) :
    (P -∗ Φ #b1) ⊢ P -∗ Φ #b2 := by
  rw [h]

theorem ValidCluster.wp_proof (wp_ValidAddrs : ValidAddrs.spec (GF := GF) (hG := hG)) : ValidCluster.spec (GF := GF) (hG := hG) := by
  intro addrs dq l voters msz mcs mif hlen
  wp_start as Hsl
  try wp_auto
  wp_apply wp_ValidAddrs _ _ _ _ hlen $$ [$Hsl] as Hsl
  try wp_auto
  cases hv : validAddrs l (uint.nat voters)
  all_goals repeat (first | wp_if_destruct | wp_auto)
  all_goals repeat (first | wp_if_destruct | wp_auto)
  all_goals repeat (first | wp_if_destruct | wp_auto)
  all_goals
    irevert HΦ
    unfold validCluster
    rw [hv]
    iintro HΦ
    iapply (wand_bool_congr (addrs ↦*{dq} l) Φ _ _
      (by first | rfl | (simp; done) | (simp_all; done) | (simp_all [decide_eq_decide]; word))) $$ HΦ
    iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
