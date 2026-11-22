/-
Proof of `Spec/github_com/Masterminds/semver/v3/comparePrerelease.lean` over the real code
(prove-ps2-semver, 2026-11-22), over the specs of `strings.Split` and `comparePrePart`.
-/
module

public import Spec.github_com.Masterminds.semver.v3.comparePrerelease
public import Spec.github_com.Masterminds.semver.v3.comparePrePart
public import Perennial.Spec.strings.Split

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

theorem semver.comparePrerelease.wp_proof
    (wp_Split : _root_.Perennial.strings.Split.spec (GF := GF) (hG := hG))
    (wp_comparePrePart : semver.comparePrePart.spec (GF := GF) (hG := hG)) :
    semver.comparePrerelease.spec (GF := GF) (hG := hG) := by
  intro v o
  wp_start as -
  ihave #Hss : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_Split v go!"." (by decide)) as %sl ⟨Hsl, -⟩
  wp_apply (wp_Split o go!"." (by decide)) as %ol ⟨Hol, -⟩
  ihave %HlS := ownSlice_len $$ Hsl
  ihave %HlO := ownSlice_len $$ Hol
  unfold semver.cmpPre
  generalize strings.split v go!"." = SP at *
  generalize strings.split o go!"." = OP at *
  wp_join iprop(∃ lv : w64, l_ptr ↦ lv ∗ olen_ptr ↦ ol.len ∗
      ⌜sint.Z lv = max (sint.Z sl.len) (sint.Z ol.len)⌝) with [l olen] as ⟨%lv, l, olen, %Hlv⟩
  · iexists _; iframe; ipureintro; exact (Int.max_eq_right (Int.le_of_lt Hif)).symm
  · iexists _; iframe; ipureintro; exact (Int.max_eq_left (Int.not_lt.mp Hif)).symm
  ihave HI : (∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "Hsl" ∷ sl ↦* SP ∗
      "Hol" ∷ ol ↦* OP ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z lv ∧
        semver.cmpParts (SP.drop (sint.nat i)) (OP.drop (sint.nat i)) = semver.cmpParts SP OP⌝ :
        IProp GF) $$ [i Hsl Hol]
  · iexists (W64 0)
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  obtain ⟨Hi0, Hil, Heq⟩ := Hi
  wp_if_destruct
  · have Hil' : sint.Z i < sint.Z lv := Hif
    have Hlt : sint.nat i < SP.length ∨ sint.nat i < OP.length := by
      rw [HlS.1, HlO.1]
      rcases Int.le_total (sint.Z sl.len) (sint.Z ol.len) with h | h
      · right; rw [Int.max_eq_right h] at Hlv; word
      · left; rw [Int.max_eq_left h] at Hlv; word
    have Hstep := semver.cmpParts_drop SP OP (sint.nat i) Hlt
    have Hn1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have Hz1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z lv := by word
    wp_join iprop(stemp_ptr ↦ SP[sint.nat i]?.getD [] ∗ sl ↦* SP ∗ sparts_ptr ↦ sl ∗ i_ptr ↦ i)
      with [stemp Hsl sparts i] as ⟨stemp, Hsl, sparts, i⟩
    · rw [ite_eq_left ⟨Hi0, Hif⟩]
      list_elem SP (sint.nat i) as a
      wp_apply wp_load_slice_index sl (sint.Z i) SP (DFrac.own 1) a Hi0 $$ [Hsl] as Hsl
      · iframe; ipureintro; exact Ha_lookup
      have Hst : SP[sint.nat i]?.getD [] = a := by rw [Ha_lookup]; rfl
      rw [Hst]
      wp_join_done
    · have hge : SP.length ≤ sint.nat i := by rw [HlS.1]; word
      have Hst : SP[sint.nat i]?.getD [] = [] := by
        rw [List.getElem?_eq_none hge]; rfl
      rw [Hst]
      iframe
    wp_join iprop(otemp_ptr ↦ OP[sint.nat i]?.getD [] ∗ ol ↦* OP ∗ oparts_ptr ↦ ol ∗ i_ptr ↦ i)
      with [otemp Hol oparts i] as ⟨otemp, Hol, oparts, i⟩
    · rw [ite_eq_left ⟨Hi0, Hif⟩]
      list_elem OP (sint.nat i) as a
      wp_apply wp_load_slice_index ol (sint.Z i) OP (DFrac.own 1) a Hi0 $$ [Hol] as Hol
      · iframe; ipureintro; exact Ha_lookup
      have Hst : OP[sint.nat i]?.getD [] = a := by rw [Ha_lookup]; rfl
      rw [Hst]
      wp_join_done
    · have hge : OP.length ≤ sint.nat i := by rw [HlO.1]; word
      have Hst : OP[sint.nat i]?.getD [] = [] := by
        rw [List.getElem?_eq_none hge]; rfl
      rw [Hst]
      iframe
    wp_apply wp_comparePrePart
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (i + W64 1)
      iframe
      ipureintro
      refine ⟨Hz1.1, Hz1.2, ?_⟩
      rw [Hn1, ← Heq, Hstep, ite_eq_left Hif]
    · have Hret : semver.cmpParts SP OP =
          semver.cmpPrePart (SP[sint.nat i]?.getD []) (OP[sint.nat i]?.getD []) := by
        rw [← Heq, Hstep, ite_eq_right Hif]
      wp_for_post
      rw [Hret]
      iapply HΦ; itrivial
  · have Hge : SP.length ≤ sint.nat i ∧ OP.length ≤ sint.nat i := by
      rw [HlS.1, HlO.1]
      rcases Int.le_total (sint.Z sl.len) (sint.Z ol.len) with h | h
      · rw [Int.max_eq_right h] at Hlv; constructor <;> word
      · rw [Int.max_eq_left h] at Hlv; constructor <;> word
    have h0 : semver.cmpParts SP OP = W64 0 := by
      rw [← Heq]; exact semver.cmpParts_drop_end SP OP (sint.nat i) Hge
    rw [h0]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
