/-
`fieldpath.Set.Has`: proved over its callees' specs (the hypotheses): the loop descends the
children (`SetNodeMap.Get`) re-slicing the lent path (`p = p[1:]`), keeping the rest of the path's
membership in the current set equal to the whole path's in `S`, and the way back to the caller's
slice (a wand over the split slice).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.Set.Has.wp_proof
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_SetNodeMap_Get : fieldpath.SetNodeMap.Get.spec (GF := GF)) :
    fieldpath.Set.Has.spec (GF := GF) := fun p S s dq q => by
  wp_start as ⟨#Hs, Hq⟩
  unfold isPathF isPEs
  icases Hq with ⟨%es, Hes, #Hpes⟩
  ihave %hl := fpL.isPEL_length $$ Hpes
  ihave %hsl := ownSlice_len $$ Hes
  ihave %hne := isSet_ne_law_holds p S $$ Hs
  wp_auto
  wp_if_destruct
  · have hq : q = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← hl, hsl.1, Hif]; rfl
    subst hq
    iapply HΦ
    isplitl [Hes]
    · iexists es; iframe; iexact Hpes
    ipureintro; simp only [Bool.false_eq_true, false_iff]; exact hne
  ihave HI : (∃ (k : w64) (sl : GoSlice) (sp : Loc) (T : PathSet),
      "p" ∷ p_ptr ↦ sl ∗ "s" ∷ s_ptr ↦ sp ∗ "#HT" ∷ isSet sp T ∗
      "Hsl" ∷ sl ↦*{dq} es.drop (sint.nat k) ∗ "Hback" ∷ (sl ↦*{dq} es.drop (sint.nat k) -∗ s ↦*{dq} es) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k < q.length ∧ (q.drop (sint.nat k) ∈ T ↔ q ∈ S)⌝ : IProp GF)
      $$ [p s Hes]
  · iexists W64 0, s, p, S
    iframe #
    iframe
    isplitl
    · iintro H; iexact H
    ipureintro
    refine ⟨by decide, ?_, by rfl⟩
    have : s.len ≠ W64 0 := Hif
    have : 0 < sint.nat s.len := by word
    show 0 < _; omega
  wp_for HI
  obtain ⟨hk0, hk, hkT⟩ := Hk
  have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
  ihave %hlk := ownSlice_len $$ Hsl
  have hkl : sint.nat k < es.length := by omega
  list_elem es (sint.nat k) as e
  have he0 : (es.drop (sint.nat k))[(0 : Int).toNat]? = some e := by
    simp only [Int.toNat_zero, List.getElem?_drop, Nat.add_zero]; exact He_lookup
  icases fpL.isPEL_lookup es q (sint.nat k) e He_lookup $$ Hpes with ⟨%a, %ha, #Ha⟩
  have hqd : q.drop (sint.nat k) = a :: q.drop (sint.nat k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
    rw [List.getElem?_eq_getElem hk] at ha
    rw [Option.some.inj ha]
  icases isSet_split_law_holds sp T $$ HT with ⟨#HTm, #HTc⟩
  have hsl0 : 0 < sint.Z sl.len := by
    have : 0 < (es.drop (sint.nat k)).length := by simp; omega
    rw [hlk.1] at this; word
  wp_if_destruct
  · have hq1 : q.drop (sint.nat k + 1) = [] := by
      have : (es.drop (sint.nat k)).length = 1 := by rw [hlk.1, Hif]; rfl
      simp at this ⊢; omega
    rw [hq1] at hqd
    simp only [show (0 : Int) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by decide, hsl0⟩,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) _ dq e (by decide)) $$ [$Hsl] as Hsl
    · ipureintro; exact he0
    wp_apply (h_PathElementSet_Has (sp.[fieldpath.Set', go!"Members"]) DFrac.discard T.tops e a) $$ [$HTm $Ha] as %r ⟨-, %hr⟩
    wp_for_post
    iapply HΦ
    isplitl [Hsl Hback]
    · iexists es; isplitl
      · iapply Hback; iexact Hsl
      iexact Hpes
    ipureintro
    rw [hr, ← hkT, hqd, fpC.mem_tops]
  · have hrest : q.drop (sint.nat k + 1) ≠ [] := by
      have h2 : (es.drop (sint.nat k)).length ≠ 1 := by
        rw [hlk.1]; intro h; apply Hif; word
      simp at h2 ⊢; omega
    simp only [show (0 : Int) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by decide, hsl0⟩,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) _ dq e (by decide)) $$ [$Hsl] as Hsl
    · ipureintro; exact he0
    wp_apply (h_SetNodeMap_Get (sp.[fieldpath.Set', go!"Children"]) T.deep e a) $$ [$HTc $Ha] as %q' %ok ⟨%hok, Hq'⟩
    have hmemT : q.drop (sint.nat k) ∈ T ↔ q.drop (sint.nat k + 1) ∈ T.under a := by
      rw [hqd, fpC.mem_under]; exact ⟨fun h => ⟨hrest, h⟩, fun h => h.2⟩
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iapply HΦ
      isplitl [Hsl Hback]
      · iexists es; isplitl
        · iapply Hback; iexact Hsl
        iexact Hpes
      ipureintro
      simp only [Bool.false_eq_true, false_iff]
      intro hq
      rw [← hkT, hqd] at hq
      have hlen2 : 2 ≤ (a :: q.drop (sint.nat k + 1)).length := by
        cases h : q.drop (sint.nat k + 1) with
        | nil => exact absurd h hrest
        | cons _ _ => simp
      have hh : a ∈ T.deep.heads :=
        (fpC.mem_heads _ _).2 ⟨_, hrest, (fpC.mem_deep _ _).2 ⟨hq, hlen2⟩⟩
      exact absurd (hok.2 hh) (by simp)
    · simp only [↓reduceIte]
      wp_auto
      ihave %hwf := ownSlice_wf $$ Hsl
      have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap :=
        ⟨by decide, by word, hwf.2⟩
      rw [if_pos hb1]
      icases (ownSlice_slice (W64 1) sl.len sl dq (es.drop (sint.nat k))
        ⟨by decide, by word, Int.le_refl _⟩).1 $$ Hsl with ⟨H0, Hmid, H3⟩
      have hsub : subslice (sint.nat (W64 1)) (sint.nat sl.len) (es.drop (sint.nat k)) =
          es.drop (sint.nat (k + W64 1)) := by
        unfold subslice
        rw [List.take_of_length_le (Nat.le_of_eq hlk.1), List.drop_drop, hk1]
        rfl
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, slice.slice sl fieldpath.PathElement (W64 1) sl.len, q', T.deep.under a
      iframe
      rw [← hsub]
      iframe
      isplitl
      · iintro Hmid
        iapply Hback
        iapply (ownSlice_slice (W64 1) sl.len sl dq (es.drop (sint.nat k))
          ⟨by decide, by word, Int.le_refl _⟩).2
        iframe
      ipureintro
      rw [hk1, fpS.under_deep, ← hmemT]
      refine ⟨by word, ?_, hkT⟩
      have := List.length_pos_iff.2 hrest
      simp at this; omega


end proof

end smd
end EtcdGrove
end Perennial
