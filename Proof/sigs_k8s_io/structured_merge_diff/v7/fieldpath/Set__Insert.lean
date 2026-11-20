/-
`fieldpath.Set.Insert`: proved over its callees' specs (the hypotheses). The loop holds the
current set owned (`trieOwn`, canonical, its paths no more than the whole set's) and a wand putting
back a new version of it, with the rest of the path added, into the whole owned set; each descent
(`SetNodeMap.Descend`) composes the wand (`fpI.descend_step`), the last element goes in the
members (`fpI.members_step`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Descend
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsInsert

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

theorem fieldpath.Set.Insert.wp_proof
    (h_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (h_SetNodeMap_Descend : fieldpath.SetNodeMap.Descend.spec (GF := GF)) :
    fieldpath.Set.Insert.spec (GF := GF) := fun p S s dq q => by
  wp_start as ⟨HS, Hq, %hc⟩
  unfold isPathF isPEs
  icases Hq with ⟨%es, Hes, #Hpes⟩
  ihave %hl := fpL.isPEL_length $$ Hpes
  ihave %hsl := ownSlice_len $$ Hes
  unfold ownSet
  icases HS with ⟨%t, %ht, Ht⟩
  have htS : fpC.tset t = S := FSet.ext' (fun x => by rw [fpC.mem_tset, ht.2])
  wp_auto
  wp_if_destruct
  · have hq : q = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← hl, hsl.1, Hif]; rfl
    subst hq
    iapply HΦ
    isplitl [Ht]
    · iexists t
      iframe
      ipureintro
      refine ⟨ht.1, fun x => ?_⟩
      rw [ht.2]
      show _ ↔ x ∈ FSet.union S (FSet.ofList ([[]].filter (fun p => !p.isEmpty)))
      rw [FSet.mem_union', FSet.mem_ofList']
      simp
    · iexists es; iframe; iexact Hpes
  ihave HI : (∃ (k : w64) (sl : GoSlice) (c : Loc) (tc : Trie),
      "p" ∷ p_ptr ↦ sl ∗ "s" ∷ s_ptr ↦ c ∗ "Htc" ∷ trieOwn c tc ∗
      "Hsl" ∷ sl ↦*{dq} es.drop (sint.nat k) ∗ "Hback" ∷ (sl ↦*{dq} es.drop (sint.nat k) -∗ s ↦*{dq} es) ∗
      "HW" ∷ (∀ tc', trieOwn c tc' -∗
        ⌜Trie.Canonical tc' ∧ ∀ x, Trie.paths tc' x ↔ Trie.paths tc x ∨ x = q.drop (sint.nat k)⌝ -∗
        ∃ t', ⌜t'.Canonical ∧ ∀ x, t'.paths x ↔ x ∈ PathSet.union S (PathSet.single q)⌝ ∗ trieOwn p t') ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k < q.length ∧ Trie.Canonical tc ∧
        (fpC.tset tc).card ≤ S.card⌝ : IProp GF)
      $$ [p s Hes Ht]
  · iexists W64 0, s, p, t
    iframe
    isplitl
    · iintro H; iexact H
    isplitl
    · iintro %tc' Htc' %h
      iexists tc'
      iframe
      ipureintro
      refine ⟨h.1, fun x => ?_⟩
      have hqne : q ≠ [] := by
        intro h0; apply Hif
        have h1 : sint.nat s.len = 0 := by rw [← hsl.1, hl, h0]; rfl
        have h2 := hsl.2
        word
      rw [h.2, ht.2]
      show _ ↔ x ∈ FSet.union S (FSet.ofList ([q].filter (fun p => !p.isEmpty)))
      rw [FSet.mem_union', FSet.mem_ofList']
      have e0 : sint.nat (W64 0) = 0 := rfl
      rw [e0, List.drop_zero]
      cases q with
      | nil => exact absurd rfl hqne
      | cons _ _ => simp
    ipureintro
    refine ⟨by decide, ?_, ht.1, by rw [htS]; exact Nat.le_refl _⟩
    have : s.len ≠ W64 0 := Hif
    have : 0 < sint.nat s.len := by word
    show 0 < _; omega
  wp_for HI
  obtain ⟨hk0, hk, hcan, hcard⟩ := Hk
  have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
  ihave %hlk := ownSlice_len $$ Hsl
  have hkl : sint.nat k < es.length := by omega
  list_elem es (sint.nat k) as e
  have he0 : (es.drop (sint.nat k))[(0 : Int).toNat]? = some e := by
    simp only [Int.toNat_zero, List.getElem?_drop, Nat.add_zero]; exact He_lookup
  icases fpL.isPEL_lookup es q (sint.nat k) e He_lookup $$ Hpes with ⟨%a, %ha, #Ha⟩
  ihave %haw := fpL.isPE_wf' e a $$ Ha
  have hqd : q.drop (sint.nat k) = a :: q.drop (sint.nat k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
    rw [List.getElem?_eq_getElem hk] at ha
    rw [Option.some.inj ha]
  have hsl0 : 0 < sint.Z sl.len := by
    have : 0 < (es.drop (sint.nat k)).length := by simp; omega
    rw [hlk.1] at this; word
  have hSc : S.card < 2 ^ 63 - 1 := hc
  obtain ⟨ms, cs⟩ := tc
  icases fpI.trieOwn_open c ms cs hcan.1 $$ Htc with ⟨%hwc, HM, HN, Hop⟩
  wp_if_destruct
  · -- the last element: into the members
    have hq1 : q.drop (sint.nat k + 1) = [] := by
      have : (es.drop (sint.nat k)).length = 1 := by rw [hlk.1, Hif]; rfl
      simp at this ⊢; omega
    rw [hq1] at hqd
    simp only [show (0 : Int) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by decide, hsl0⟩,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) _ dq e (by decide)) $$ [$Hsl] as Hsl
    · ipureintro; exact he0
    have hmc := Nat.le_trans (fpI.card_members ms cs) hcard
    wp_apply (h_PathElementSet_Insert (c.[fieldpath.Set', go!"Members"]) (FSet.ofList ms) e a)
      $$ [$HM $Ha] as HM
    · ipureintro; show FSet.card _ < _; omega
    icases Hop $$ HM HN with ⟨%ms', %hms', Htc⟩
    obtain ⟨hcan', hpaths'⟩ := fpI.members_step hcan hms'.1 hms'.2
    have hfin : Trie.Canonical (Trie.mk ms' cs) ∧ ∀ x, Trie.paths (Trie.mk ms' cs) x ↔
        Trie.paths (Trie.mk ms cs) x ∨ x = q.drop (sint.nat k) := ⟨hcan', fun x => by rw [hpaths', hqd]⟩
    ihave Hres := HW $$ Htc %hfin
    wp_for_post
    iapply HΦ
    iframe
    iexists es; isplitl
    · iapply Hback; iexact Hsl
    iexact Hpes
  · have hrest : q.drop (sint.nat k + 1) ≠ [] := by
      have h2 : (es.drop (sint.nat k)).length ≠ 1 := by
        rw [hlk.1]; intro h; apply Hif; word
      simp at h2 ⊢; omega
    simp only [show (0 : Int) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by decide, hsl0⟩,
      ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) _ dq e (by decide)) $$ [$Hsl] as Hsl
    · ipureintro; exact he0
    have hcl := Nat.le_trans (fpI.card_children ms cs hcan hwc) hcard
    wp_apply (h_SetNodeMap_Descend (c.[fieldpath.Set', go!"Children"]) cs e a) $$ [$HN $Ha]
      as %q' ⟨%tch, %hlkc, Htch, Hwd⟩
    · ipureintro; exact ⟨hcan.2.1, by omega⟩
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
    have hcanch : Trie.Canonical tch := by
      rcases hlkc with h | ⟨-, rfl⟩
      · exact (fpC.canonicalC_mem cs a tch hcan.2.2 (fpI.lookup_mem a cs tch h)).1
      · exact fpI.canon_empty
    have hcardch : (fpC.tset tch).card ≤ S.card := by
      rcases hlkc with h | ⟨-, rfl⟩
      · exact Nat.le_trans (fpI.card_child ms cs a tch h) hcard
      · rw [fpI.tset_empty_card]; exact Nat.zero_le _
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, slice.slice sl fieldpath.PathElement (W64 1) sl.len, q', tch
    iframe
    rw [← hsub]
    iframe
    isplitl [H0 H3 Hback]
    · iintro Hmid
      iapply Hback
      iapply (ownSlice_slice (W64 1) sl.len sl dq (es.drop (sint.nat k))
        ⟨by decide, by word, Int.le_refl _⟩).2
      iframe
    isplitl [HW Hwd Hop HM]
    · iintro %tq' Htq' %h
      ihave HN := Hwd $$ Htq'
      icases Hop $$ HM HN with ⟨%ms', %hms', Htc⟩
      rw [hk1] at h
      obtain ⟨hcan1, hp1⟩ := fpI.descend_step hcan hwc haw hlkc h.1 h.2
      obtain ⟨hcan2, hp2⟩ := fpI.members_congr hcan1 hms'.1 hms'.2
      have hfin : Trie.Canonical (Trie.mk ms' (nodesSet a tq' cs)) ∧ ∀ x,
          Trie.paths (Trie.mk ms' (nodesSet a tq' cs)) x ↔
            Trie.paths (Trie.mk ms cs) x ∨ x = q.drop (sint.nat k) :=
        ⟨hcan2, fun x => by rw [hp2, hp1, hqd]⟩
      iapply HW $$ Htc %hfin
    ipureintro
    rw [hk1]
    refine ⟨by word, ?_, hcanch, hcardch⟩
    have := List.length_pos_iff.2 hrest
    simp at this; omega

end proof

end smd
end EtcdGrove
end Perennial
