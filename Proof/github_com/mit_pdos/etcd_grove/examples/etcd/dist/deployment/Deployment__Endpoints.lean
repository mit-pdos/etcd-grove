/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/Deployment__Endpoints.lean`.
Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Endpoints

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem Deployment.Endpoints.wp_proof :
    etcd_dist.Deployment.Endpoints.spec (GF := GF) (hG := hG) := by
  intro v d
  wp_start as #Hd
  wp_auto
  iunfold deploymentRepr at Hd
  icases Hd with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hm
  rw [List.length_map] at Hlen
  ihave HI : (∃ (k : Nat) (mv : deployment.Member) (esl : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "m" ∷ m_ptr ↦ mv ∗ "eps" ∷ eps_ptr ↦ esl ∗
      "Heps" ∷ esl ↦* (d.members.take k).map Member.client ∗
      "Hcap" ∷ ownSliceCap GoString esl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜k ≤ d.members.length⌝ : IProp GF)
    $$ [i m eps]
  · iexists 0, _, slice.nil
    iframe
    isplitl []
    · simp only [List.take_zero, List.map_nil]
      iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    omega
  wp_for HI
  wp_if_destruct
  · have hk : k < d.members.length := by word
    have hc : sint.Z (W64 (k : Int)) < sint.Z v.Members'.len := by word
    have h0 : 0 ≤ sint.Z (W64 (k : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsk : (sint.Z (W64 (k : Int))).toNat = k := by word
    obtain ⟨mm, hmm⟩ : ∃ mm, d.members[k]? = some mm := ⟨_, List.getElem?_eq_getElem hk⟩
    wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 (k : Int))) (d.members.map Member.val) DFrac.discard mm.val h0) $$ [] as -
    · iframe #; ipureintro; rw [hsk, List.getElem?_map, hmm]; rfl
    wp_apply wp_slice_literal (V := GoString) [mm.client]
    isplitr
    · ipureintro; rfl
    iintro %csl ⟨Hcsl, -⟩
    wp_apply (wp_slice_append esl _ _ [mm.client] (DFrac.own 1)) $$ [Heps Hcap Hcsl] as %esl2 ⟨Heps, Hcap, -⟩
    · iframe
    have hwk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by
      rw [show ((k + 1 : Nat) : Int) = (k : Int) + 1 by omega, W64, W64, W64, BitVec.ofInt_add]
    wp_for_post
    iframe
    iexists (k + 1), _, esl2
    rw [hwk, List.take_add_one, hmm, Option.toList_some, List.map_append]
    iframe
    ipureintro
    exact hk
  · have hkl : k = d.members.length := by word
    subst hkl
    rw [List.take_length]
    iapply HΦ
    iframe
end proof

end etcd_dist
end EtcdGrove
end Perennial
