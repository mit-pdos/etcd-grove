module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.decodeObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem decodeObj.wp_proof : decodeObj.spec (GF := GF) (hG := hG) := by
  intro sl dq d
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  (try wp_auto)
  wp_if_destruct
  · -- too short
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD; rw [if_pos (by word)]
    rw [this]
  -- the tag
  icases (ownSlice_slice (W64 0) (W64 3) sl dq d ⟨by word, by word, by word⟩).1 $$ Hs
    with ⟨H0, Ht, H3⟩
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 3) ∧
    sint.Z (W64 3) ≤ sint.Z sl.cap by word)]
  wp_apply wp_bytes_to_string _ _ dq $$ [$Ht] as Ht
  ihave Hs := (ownSlice_slice (W64 0) (W64 3) sl dq d ⟨by word, by word, by word⟩).2 $$ [H0 Ht H3]
  · rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 3) = 3 from rfl]
    iframe H0 H3 Ht
  have hsub : subslice 0 3 d = d.take 3 := by
    unfold subslice; simp
  simp only [hsub]
  have hnl : ¬ d.length < 4 := by word
  by_cases hv1 : d.take 3 = tagV1
  · have hd1 : decide (d.take 3 = go!"v1:") = true := by simp only [decide_eq_true_eq]; exact hv1
    rw [hd1]
    (try wp_auto)
    rw [if_pos (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z sl.len by word)]
    have h3 : d[(sint.Z (W64 3)).toNat]? = some (d.getD 3 (W8 0)) := by
      rw [show (sint.Z (W64 3)).toNat = 3 from rfl, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by word)]
      rfl
    wp_apply wp_load_slice_index sl (sint.Z (W64 3)) d dq _ (by word) $$ [$Hs] as Hs
    · ipureintro; exact h3
    (try wp_auto)
    (try wp_auto)
    have hnb : uint.Z (d.getD 3 (W8 0)) < 256 := by
      have := (d.getD 3 (W8 0)).isLt; simp only [uint.Z]; omega
    have hlen : (d.length : Int) = sint.Z sl.len := by rw [Hl.1]; word
    have hcap := Hwf.2
    have htagok : ¬ (d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0) := fun h => h.1 hv1
    have hhi : sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) = 4 + uint.Z (d.getD 3 (W8 0)) := by
      word
    wp_if_destruct
    · -- the name runs past the data
      (try wp_auto)
      iapply HΦ
      iframe Hs
      ipureintro
      have : decodeD d = none := by
        unfold decodeD
        rw [if_neg hnl, if_neg htagok, if_pos (by simp only [uint.Z] at hhi hnb; word)]
      rw [this]
    · rw [if_pos (show 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
        sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.cap by word)]
      have hb1 : 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
          sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.len := by word
      icases (ownSlice_slice (W64 4) (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl dq d hb1).1 $$ Hs
        with ⟨A, B, C⟩
      wp_apply wp_bytes_to_string _ _ dq $$ [$B] as B
      ihave Hs := (ownSlice_slice (W64 4) (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl dq d hb1).2
        $$ [A B C]
      · (try rw [show sint.nat (W64 4) = 4 from rfl])
        iframe A B C
      (try wp_auto)
      rw [if_pos (show 0 ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
          sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.cap by word)]
      have hb2 : 0 ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
          sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.len := by word
      icases (ownSlice_slice (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl.len sl dq d hb2).1 $$ Hs
        with ⟨A, B, C⟩
      wp_apply wp_bytes_to_string _ _ dq $$ [$B] as B
      ihave Hs := (ownSlice_slice (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl.len sl dq d hb2).2
        $$ [A B C]
      · (try rw [show sint.nat (W64 4) = 4 from rfl])
        iframe A B C
      (try wp_auto)
      iapply HΦ
      iframe Hs
      ipureintro
      have hn4 : sint.nat (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) = 4 + (d.getD 3 (W8 0)).toNat := by
        simp only [uint.Z] at hhi; word
      have hdec : decodeD d = some ((d.drop 4).take (d.getD 3 (W8 0)).toNat,
          d.drop (4 + (d.getD 3 (W8 0)).toNat)) := by
        unfold decodeD
        rw [if_neg hnl, if_neg htagok, if_neg (by simp only [uint.Z] at hhi hnb; word)]
      rw [hdec]
      refine ⟨rfl, ?_, ?_⟩
      · rw [hn4]
        unfold subslice
        rw [List.drop_take]
        congr 1
        omega
      · rw [hn4, show sint.nat sl.len = d.length by word]
        unfold subslice
        rw [List.take_of_length_le (by omega)]
  by_cases hv0 : d.take 3 = tagV0
  · have hd1 : decide (d.take 3 = go!"v1:") = false := by simp only [decide_eq_false_iff_not]; exact hv1
    have hd0 : decide (d.take 3 = go!"v0:") = true := by simp only [decide_eq_true_eq]; exact hv0
    rw [hd1]
    (try wp_auto)
    rw [hd0]
    (try wp_auto)
    rw [if_pos (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z sl.len by word)]
    have h3 : d[(sint.Z (W64 3)).toNat]? = some (d.getD 3 (W8 0)) := by
      rw [show (sint.Z (W64 3)).toNat = 3 from rfl, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by word)]
      rfl
    wp_apply wp_load_slice_index sl (sint.Z (W64 3)) d dq _ (by word) $$ [$Hs] as Hs
    · ipureintro; exact h3
    (try wp_auto)
    (try wp_auto)
    have hnb : uint.Z (d.getD 3 (W8 0)) < 256 := by
      have := (d.getD 3 (W8 0)).isLt; simp only [uint.Z]; omega
    have hlen : (d.length : Int) = sint.Z sl.len := by rw [Hl.1]; word
    have hcap := Hwf.2
    have htagok : ¬ (d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0) := fun h => h.2 hv0
    have hhi : sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) = 4 + uint.Z (d.getD 3 (W8 0)) := by
      word
    wp_if_destruct
    · -- the name runs past the data
      (try wp_auto)
      iapply HΦ
      iframe Hs
      ipureintro
      have : decodeD d = none := by
        unfold decodeD
        rw [if_neg hnl, if_neg htagok, if_pos (by simp only [uint.Z] at hhi hnb; word)]
      rw [this]
    · rw [if_pos (show 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
        sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.cap by word)]
      have hb1 : 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
          sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.len := by word
      icases (ownSlice_slice (W64 4) (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl dq d hb1).1 $$ Hs
        with ⟨A, B, C⟩
      wp_apply wp_bytes_to_string _ _ dq $$ [$B] as B
      ihave Hs := (ownSlice_slice (W64 4) (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl dq d hb1).2
        $$ [A B C]
      · (try rw [show sint.nat (W64 4) = 4 from rfl])
        iframe A B C
      (try wp_auto)
      rw [if_pos (show 0 ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
          sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.cap by word)]
      have hb2 : 0 ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
          sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.len := by word
      icases (ownSlice_slice (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl.len sl dq d hb2).1 $$ Hs
        with ⟨A, B, C⟩
      wp_apply wp_bytes_to_string _ _ dq $$ [$B] as B
      ihave Hs := (ownSlice_slice (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) sl.len sl dq d hb2).2
        $$ [A B C]
      · (try rw [show sint.nat (W64 4) = 4 from rfl])
        iframe A B C
      (try wp_auto)
      iapply HΦ
      iframe Hs
      ipureintro
      have hn4 : sint.nat (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) = 4 + (d.getD 3 (W8 0)).toNat := by
        simp only [uint.Z] at hhi; word
      have hdec : decodeD d = some ((d.drop 4).take (d.getD 3 (W8 0)).toNat,
          d.drop (4 + (d.getD 3 (W8 0)).toNat)) := by
        unfold decodeD
        rw [if_neg hnl, if_neg htagok, if_neg (by simp only [uint.Z] at hhi hnb; word)]
      rw [hdec]
      refine ⟨rfl, ?_, ?_⟩
      · rw [hn4]
        unfold subslice
        rw [List.drop_take]
        congr 1
        omega
      · rw [hn4, show sint.nat sl.len = d.length by word]
        unfold subslice
        rw [List.take_of_length_le (by omega)]
  · have hd1 : decide (d.take 3 = go!"v1:") = false := by simp only [decide_eq_false_iff_not]; exact hv1
    have hd0 : decide (d.take 3 = go!"v0:") = false := by
      simp only [decide_eq_false_iff_not]; exact hv0
    rw [hd1]
    (try wp_auto)
    rw [hd0]
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD
      rw [if_neg hnl, if_pos ⟨hv1, hv0⟩]
    rw [this]

end proof

end k8setcd3
end EtcdGrove
end Perennial
