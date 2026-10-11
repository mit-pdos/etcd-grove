/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/tick.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.tick
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

theorem tick.wp_proof (wp_node_Tick : node.Tick.spec (GF := GF) (hG := hG)) :
    tick.spec (GF := GF) (hG := hG) := by
  intro γn id n
  wp_start as ⟨#HisNode, Hcred⟩
  wp_auto
  ihave IH : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗ "Hcred" ∷ tickCred γn.bud (ticksN - sint.nat k) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ticksN : Int)⌝) $$ [i Hcred]
  · iexists W64 0
    iframe i
    simp only [show sint.nat (W64 0) = 0 by rfl, Nat.sub_zero]
    iframe Hcred
    ipureintro; unfold ticksN; constructor <;> word
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ticksN := by unfold ticksN at *; word
    rw [show ticksN - sint.nat k = 1 + (ticksN - (sint.nat k + 1)) by omega]
    icases (tickCred_split γn.bud 1 _).1 $$ Hcred with ⟨Hc1, Hcred⟩
    wp_apply time.wp_Sleep
    wp_apply wp_node_Tick γn id n $$ [$HisNode $Hc1]
    wp_for_post
    iframe
    iexists k + W64 1
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by unfold ticksN at *; word]
    iframe
    ipureintro; unfold ticksN at *; constructor <;> word
  · iapply HΦ
    itrivial

end proof

end register
end EtcdGrove
end Perennial
