/- Lean-first (no Rocq counterpart). The proof of `walSaveSnap`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walSaveSnap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem walSaveSnap.wp_proof : walSaveSnap.spec (GF := GF) (hG := hG) := by
  intro v c idx term
  wp_start as Hc
  iunfold contentsRep at Hc
  icases Hc with ⟨%Hf, #Hs⟩
  obtain ⟨hhs, hbi, hbt⟩ := Hf
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · wp_end
    have h1 : uint.nat idx < uint.nat c.baseIdx := by rw [← hbi]; word
    simp only [tSaveSnap, h1, ↓reduceIte, contentsRep]
    isplitr
    · ipureintro; exact ⟨hhs, hbi, hbt⟩
    · iexact Hs
  have h1 : ¬ uint.nat idx < uint.nat c.baseIdx := by rw [← hbi]; intro h; apply Hif; word
  wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %e0 ⟨He0, He0cap⟩
  · ipureintro; word
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist He0
  wp_auto
  wp_if_destruct
  · have h2 : uint.nat idx ≤ uint.nat c.hs.commit' := by rw [← hhs]; word
    ihave HI : (∃ (j : w64) (o : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "ents" ∷ ents_ptr ↦ o ∗
        "Hout" ∷ o ↦*□ (c.ents.drop (uint.nat (idx - c.baseIdx))).take (uint.nat j - uint.nat (idx - c.baseIdx)) ∗
        "Hcap" ∷ ownSliceCap TEnt o (DFrac.own 1) ∗
        "%Hj" ∷ ⌜uint.nat (idx - c.baseIdx) ≤ uint.nat j ∧
          (uint.nat (idx - c.baseIdx) ≤ c.ents.length → uint.nat j ≤ c.ents.length)⌝ : IProp GF)
        $$ [i ents He0 He0cap]
    · iexists idx - v.baseIdx', e0
      rw [hbi]
      simp only [Nat.sub_self, List.take_zero]
      iframe
      isplitl []
      · iexact He0
      ipureintro; omega
    wp_for HI
    wp_if_destruct
    · have Hif' := Hif
      have hjl : uint.nat j < c.ents.length := by
        have : c.ents.length = sint.nat v.ents'.len := Hlen.1
        word
      obtain ⟨x, Hx⟩ : ∃ x, c.ents[uint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.ents'.len := by
        have : c.ents.length = sint.nat v.ents'.len := Hlen.1
        constructor <;> word
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index v.ents' (sint.Z j) c.ents DFrac.discard x hb.1 as -
      · isplitl []
        · iexact Hs
        ipureintro
        rw [show (sint.Z j).toNat = uint.nat j by word]; exact Hx
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_auto
      wp_apply wp_slice_append_persistent $$ [$Hout $Hcap $Hosl] as %o' ⟨Hout, Hcap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, o'
      have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
      have hsucc : uint.nat j + 1 - uint.nat (idx - c.baseIdx) =
          (uint.nat j - uint.nat (idx - c.baseIdx)) + 1 := by omega
      have hx' : (c.ents.drop (uint.nat (idx - c.baseIdx)))[uint.nat j - uint.nat (idx - c.baseIdx)]? =
          some x := by
        rw [List.getElem?_drop, show uint.nat (idx - c.baseIdx) + (uint.nat j - uint.nat (idx - c.baseIdx)) =
          uint.nat j by omega]; exact Hx
      rw [hj1, hsucc, List.take_add_one, hx']
      iframe
      ipureintro; constructor <;> omega
    · have Hif' := Hif
      have hjn : c.ents.length ≤ uint.nat j := by
        have : c.ents.length = sint.nat v.ents'.len := Hlen.1
        word
      rw [List.take_of_length_le (by simp; omega)]
      wp_end
      simp only [tSaveSnap, h1, h2, ↓reduceIte, contentsRep]
      isplitr
      · ipureintro; simp [hhs]
      · iexact Hout
  · have h2 : ¬ uint.nat idx ≤ uint.nat c.hs.commit' := by rw [← hhs]; intro h; apply Hif; word
    wp_end
    simp only [tSaveSnap, h1, h2, ↓reduceIte, contentsRep]
    isplitr
    · ipureintro; simp [hhs]
    · iexact He0

end proof

end etcd_wal
end EtcdGrove
end Perennial
