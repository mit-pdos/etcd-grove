module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- Converts `data[L:H]` to a string, splitting `Hs` around it and joining it back. -/
local macro "slice_str " L:term:max H:term:max : tactic => `(tactic| (
  rw [if_pos (show 0 ≤ sint.Z $L ∧ sint.Z $L ≤ sint.Z $H ∧ sint.Z $H ≤ sint.Z sl.cap by
    (try simp only [hz4, h4z, hhi, hhi2]); omega)]
  icases (ownSlice_slice $L $H sl dq d (by (try simp only [hz4, h4z, hhi, hhi2]); omega)).1 $$ Hs
    with ⟨A, B, C⟩
  wp_apply wp_bytes_to_string _ _ dq $$ [B] as B
  · iexact B
  ihave Hs := (ownSlice_slice $L $H sl dq d (by (try simp only [hz4, h4z, hhi, hhi2]); omega)).2
    $$ [A B C]
  · iframe A B C
  (try wp_auto)))

set_option hygiene false in
/-- `decodeObj` after a good tag: the two length bytes, then the three strings. -/
local macro "decode_rest" : tactic => `(tactic| (
  rw [if_pos (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z sl.len by word)]
  have h3 : d[(sint.Z (W64 3)).toNat]? = some (d.getD 3 (W8 0)) := by
    rw [show (sint.Z (W64 3)).toNat = 3 from rfl, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by word)]
    rfl
  wp_apply wp_load_slice_index sl (sint.Z (W64 3)) d dq _ (by word) $$ [Hs] as Hs
  · iframe Hs; ipureintro; exact h3
  (try wp_auto)
  have hna : (uint.Z (d.getD 3 (W8 0))) = ((d.getD 3 (W8 0)).toNat : Int) := rfl
  have hnb : (d.getD 3 (W8 0)).toNat < 256 := (d.getD 3 (W8 0)).isLt
  have hhi : sint.Z (W64 5 + W64 (uint.Z (d.getD 3 (W8 0)))) =
      5 + (d.getD 3 (W8 0)).toNat := by
    rw [hna]; word
  wp_if_destruct
  · -- the name and the UID's length run past the data
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD
      rw [if_neg hnl, if_neg hbad, if_pos (by word)]
    rw [this]
  have hge : 5 + (d.getD 3 (W8 0)).toNat ≤ d.length := by word
  have h4z : sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) = 4 + (d.getD 3 (W8 0)).toNat := by
    rw [hna]; word
  rw [if_pos (show 0 ≤ sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) ∧
    sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) < sint.Z sl.len by rw [h4z]; omega)]
  have h4 : d[(sint.Z (W64 4 + W64 (uint.Z (d.getD 3 (W8 0))))).toNat]? =
      some (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)) := by
    have hlt : 4 + (d.getD 3 (W8 0)).toNat < d.length := by omega
    rw [h4z, show ((4 : Int) + ((d.getD 3 (W8 0)).toNat : Int)).toNat = 4 + (d.getD 3 (W8 0)).toNat
      by omega]
    generalize 4 + (d.getD 3 (W8 0)).toNat = k at hlt ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  wp_apply wp_load_slice_index sl _ d dq _ (by rw [h4z]; omega) $$ [Hs] as Hs
  · iframe Hs; ipureintro; exact h4
  (try wp_auto)
  have hmb : (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat < 256 :=
    (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).isLt
  have hma : (uint.Z (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0))) =
      ((d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat : Int) := rfl
  have hhi2 : sint.Z (W64 5 + W64 (uint.Z (d.getD 3 (W8 0))) +
      W64 (uint.Z (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)))) =
      5 + (d.getD 3 (W8 0)).toNat + (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat := by
    rw [hna, hma]; word
  wp_if_destruct
  · -- the UID runs past the data
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD
      rw [if_neg hnl, if_neg hbad, if_neg (by omega), if_pos (by word)]
    rw [this]
  have hge2 : 5 + (d.getD 3 (W8 0)).toNat + (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat ≤
      d.length := by rw [hhi2] at Hif; omega
  have hz4 : sint.Z (W64 4) = 4 := rfl
  slice_str (W64 4) (W64 4 + W64 (uint.Z (d.getD 3 (W8 0))))
  slice_str (W64 5 + W64 (uint.Z (d.getD 3 (W8 0))))
    (W64 5 + W64 (uint.Z (d.getD 3 (W8 0))) +
      W64 (uint.Z (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0))))
  slice_str (W64 5 + W64 (uint.Z (d.getD 3 (W8 0))) +
      W64 (uint.Z (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)))) sl.len
  iapply HΦ
  iframe Hs
  ipureintro
  have hn1 : sint.nat (W64 4 + W64 (uint.Z (d.getD 3 (W8 0)))) = 4 + (d.getD 3 (W8 0)).toNat := by
    have := h4z; word
  have hn2 : sint.nat (W64 5 + W64 (uint.Z (d.getD 3 (W8 0)))) = 5 + (d.getD 3 (W8 0)).toNat := by
    have := hhi; word
  have hn3 : sint.nat (W64 5 + W64 (uint.Z (d.getD 3 (W8 0))) +
      W64 (uint.Z (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)))) =
      5 + (d.getD 3 (W8 0)).toNat + (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat := by
    have := hhi2; word
  have hdec : decodeD d = some ((d.drop 4).take (d.getD 3 (W8 0)).toNat,
      (d.drop (5 + (d.getD 3 (W8 0)).toNat)).take
        (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat,
      d.drop (5 + (d.getD 3 (W8 0)).toNat + (d.getD (4 + (d.getD 3 (W8 0)).toNat) (W8 0)).toNat)) := by
    unfold decodeD
    rw [if_neg hnl, if_neg hbad, if_neg (by omega), if_neg (by omega)]
  rw [hdec, hn1, hn2, hn3, show sint.nat sl.len = d.length by word]
  unfold subslice
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [List.drop_take]; congr 1; omega
  · rw [List.drop_take]; congr 1; omega
  · rw [List.take_of_length_le (by omega)]))

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
  have hlen : (d.length : Int) = sint.Z sl.len := by rw [Hl.1]; word
  have hcap := Hwf.2
  by_cases hbad : d.take 3 ≠ tagV1 ∧ d.take 3 ≠ tagV0
  · rw [decide_eq_false (show ¬ d.take 3 = go!"v1:" from hbad.1)]
    (try wp_auto)
    rw [decide_eq_false (show ¬ d.take 3 = go!"v0:" from hbad.2)]
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : decodeD d = none := by
      unfold decodeD
      rw [if_neg hnl, if_pos hbad]
    rw [this]
  have htag : d.take 3 = go!"v1:" ∨ d.take 3 = go!"v0:" := by
    by_cases h : d.take 3 = go!"v1:"
    · exact Or.inl h
    · exact Or.inr (by by_cases h' : d.take 3 = go!"v0:"; exact h'; exact absurd ⟨h, h'⟩ hbad)
  rcases htag with hv | hv
  · rw [decide_eq_true hv]
    (try wp_auto)
    decode_rest
  · by_cases hv1 : d.take 3 = go!"v1:"
    · exact absurd (hv1.symm.trans hv) (by decide)
    rw [decide_eq_false hv1]
    (try wp_auto)
    rw [decide_eq_true hv]
    (try wp_auto)
    decode_rest

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
