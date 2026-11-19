/-
`fieldpath.PathElementSet.Union`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Less
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet

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

theorem fieldpath.PathElementSet.Union.wp_proof
    (h_PathElement_Less : fieldpath.PathElement.Less.spec (GF := GF)) :
    fieldpath.PathElementSet.Union.spec (GF := GF) := fun l l2 dq dq2 A B => by
  wp_start as ⟨Hs, Hs2⟩
  unfold isPESet isPESetV
  icases Hs with ⟨%v, Hl, %es, %xs, Hm, #Hx, %h⟩
  icases Hs2 with ⟨%v2, Hl2, %es2, %ys, Hm2, #Hy, %h2⟩
  icases fpA.peset_members_acc l v dq $$ Hl with ⟨Hf, Hback⟩
  icases fpA.peset_members_acc l2 v2 dq2 $$ Hl2 with ⟨Hf2, Hback2⟩
  ihave %hwx := fpL.isPEL_wf _ _ $$ Hx
  ihave %hwy := fpL.isPEL_wf _ _ $$ Hy
  ihave %hlx := fpL.isPEL_length _ _ $$ Hx
  ihave %hly := fpL.isPEL_length _ _ $$ Hy
  ihave %hsx := ownSlice_len $$ Hm
  ihave %hsy := ownSlice_len $$ Hm2
  wp_auto
  have hnx := fpA.sorted_nodup xs hwx h.1
  have hny := fpA.sorted_nodup ys hwy h2.1
  icases fpA.peset_members_upd «$r0_ptr» _ (DFrac.own 1) $$ «$r0» with ⟨Ho, Hoback⟩
  ihave Hos := ownSlice_nil (V := fieldpath.PathElement) (DFrac.own 1)
  ihave Hocap := ownSliceCap_nil (V := fieldpath.PathElement) (GF := GF)
  ihave HI : (∃ (i j : w64) (osl : GoSlice) (oes : List fieldpath.PathElement) (os : List PE),
      "i" ∷ i_ptr ↦ i ∗ "j" ∷ j_ptr ↦ j ∗
      "Ho" ∷ «$r0_ptr».[fieldpath.PathElementSet, go!"members"] ↦ osl ∗
      "Hos" ∷ osl ↦* oes ∗ "Hocap" ∷ ownSliceCap fieldpath.PathElement osl (DFrac.own 1) ∗
      "#Hoe" ∷ isPEL oes os ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.members'.len ∧
        0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v2.members'.len ∧ PE.Sorted os ∧
        fpA.Front xs ys (sint.Z i).toNat (sint.Z j).toNat ∧
        (∀ x, x ∈ os ↔ x ∈ xs.take (sint.Z i).toNat ∨ x ∈ ys.take (sint.Z j).toNat)⌝ : IProp GF)
      $$ [i j Ho Hos Hocap]
  · iexists (W64 0), (W64 0), slice.nil, [], []
    iframe
    isplitl [Hos]
    · iexact Hos
    isplitl [Hocap]
    · iexact Hocap
    isplitr
    · rw [fpL.isPEL_nil_eq]; itrivial
    ipureintro
    refine ⟨by decide, hsx.2, by decide, hsy.2, List.Pairwise.nil, fpA.front_zero xs ys, ?_⟩
    intro x; simp
  wp_for HI
  obtain ⟨hi0, hin, hj0, hjm, hos, hfr, hmem⟩ := Hinv
  wp_if_destruct
  · have hiL := Hif
    wp_if_destruct
    · have hjL := Hif
      have hix := fpA.idx_lt i _ _ hsx.1 hi0 hiL
      have hjx := fpA.idx_lt j _ _ hsy.1 hj0 hjL
      list_elem es (sint.Z i).toNat as ea
      list_elem es2 (sint.Z j).toNat as eb
      ihave ⟨%xa, %hxa, Ha⟩ := fpL.isPEL_lookup es xs _ ea Hea_lookup $$ Hx
      ihave ⟨%yb, %hyb, Hb⟩ := fpL.isPEL_lookup es2 ys _ eb Heb_lookup $$ Hy
      simp only [hj0, hjL, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v2.members' (sint.Z j) es2 dq2 eb hj0) $$ [$Hm2] as Hm2
      · ipureintro; exact Heb_lookup
      simp only [hi0, hiL, _root_.and_self, ↓reduceIte]
      wp_pures
      wp_method_call; wp_call
      wp_apply (wp_load_slice_index v.members' (sint.Z i) es dq ea hi0) $$ [$Hm] as Hm
      · ipureintro; exact Hea_lookup
      wp_apply (h_PathElement_Less ea eb xa yb) $$ [$Ha $Hb] as %r %hr
      have hixs : (sint.Z i).toNat < xs.length := by rw [← hlx]; exact hix
      have hjys : (sint.Z j).toNat < ys.length := by rw [← hly]; exact hjx
      have hxi : xs[(sint.Z i).toNat] = xa := by
        rw [List.getElem?_eq_getElem hixs] at hxa; exact Option.some.inj hxa
      have hyj : ys[(sint.Z j).toNat] = yb := by
        rw [List.getElem?_eq_getElem hjys] at hyb; exact Option.some.inj hyb
      have hsub : ∀ o ∈ os, o ∈ xs.take (sint.Z i).toNat ++ ys.take (sint.Z j).toNat := by
        intro o ho; rw [List.mem_append]; exact (hmem o).1 ho
      ihave %hoel := fpL.isPEL_length _ _ $$ Hoe
      cases r
      · have hnlt : ¬ PE.lt xa yb := fun h' => by simpa using hr.2 h'
        wp_auto
        simp only [hj0, hjL, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index v2.members' (sint.Z j) es2 dq2 eb hj0) $$ [$Hm2] as Hm2
        · ipureintro; exact Heb_lookup
        wp_apply (wp_slice_literal (V := fieldpath.PathElement) [eb])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_apply (wp_slice_append (V := fieldpath.PathElement) osl oes _ [eb] (DFrac.own 1)) $$ [$Hos $Hocap $Hlsl] as %osl' ⟨Hos, Hocap, -⟩
        simp only [hi0, hiL, hj0, hjL, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index v.members' (sint.Z i) es dq ea hi0) $$ [$Hm] as Hm
        · ipureintro; exact Hea_lookup
        simp only [hi0, hiL, hj0, hjL, _root_.and_self, ↓reduceIte]
        wp_pures
        wp_method_call; wp_call
        wp_apply (wp_load_slice_index v2.members' (sint.Z j) es2 dq2 eb hj0) $$ [$Hm2] as Hm2
        · ipureintro; exact Heb_lookup
        wp_apply (h_PathElement_Less eb ea yb xa) $$ [$Ha $Hb] as %r2 %hr2
        have hxw := hwx xa (List.mem_of_getElem? hxa)
        have hyw := hwy yb (List.mem_of_getElem? hyb)
        have hsrt : PE.Sorted (os ++ [yb]) := fpA.sorted_snoc_front hfr hos hsub yb
          (List.mem_append.2 (Or.inr (hyj ▸ fpA.getElem_mem_drop ys _ hjys)))
        have hj1 : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
        cases r2
        · -- equal elements: both advance
          have heq : xa = yb := by
            have hnlt2 : ¬ PE.lt yb xa := fun h' => by simpa using hr2.2 h'
            rcases fpA.lt_total hxw hyw with h' | h' | h'
            · exact absurd h' hnlt
            · exact h'
            · exact absurd h' hnlt2
          wp_auto
          wp_for_post
          iframe
          iexists (i + W64 1), (j + W64 1), osl', (oes ++ [eb]), (os ++ [yb])
          iframe
          isplitr
          · iapply (fpL.isPEL_app oes [eb] os [yb] hoel).2
            iframe Hoe; rw [fpL.isPEL_cons_eq, fpL.isPEL_nil_eq]; iframe Hb
          ipureintro
          have hi1 : (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1 := by word
          rw [hi1, hj1]
          refine ⟨by word, by word, by word, by word, hsrt, ?_, ?_⟩
          · exact fpA.front_step_eq h.1 h2.1 hfr hixs hjys (by rw [hxi, hyj, heq])
          · intro x
            rw [fpA.take_succ' xs _ hixs, fpA.take_succ' ys _ hjys, hxi, hyj, ← heq]
            simp only [List.mem_append, List.mem_singleton, hmem]
            constructor
            · rintro ((h | h) | h)
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
              · exact Or.inl (Or.inr h)
            · rintro ((h | h) | (h | h))
              · exact Or.inl (Or.inl h)
              · exact Or.inr h
              · exact Or.inl (Or.inr h)
              · exact Or.inr h
        · -- `yb < xa`: only `j` advances
          have hlt2 : PE.lt yb xa := hr2.1 rfl
          wp_auto
          wp_for_post
          iframe
          iexists i, (j + W64 1), osl', (oes ++ [eb]), (os ++ [yb])
          iframe
          isplitr
          · iapply (fpL.isPEL_app oes [eb] os [yb] hoel).2
            iframe Hoe; rw [fpL.isPEL_cons_eq, fpL.isPEL_nil_eq]; iframe Hb
          ipureintro
          rw [hj1]
          refine ⟨hi0, hin, by word, by word, hsrt, ?_, ?_⟩
          · refine fpA.front_step_y h2.1 hfr hjys ?_
            rw [hyj]
            exact fpA.lt_rest hwx h.1 _ hixs yb hyw (hxi ▸ hlt2)
          · intro x
            rw [fpA.take_succ' ys _ hjys, hyj]
            simp only [List.mem_append, List.mem_singleton, hmem]
            constructor
            · rintro ((h | h) | h)
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
            · rintro (h | (h | h))
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr h)
              · exact Or.inr h
      · have hlt : PE.lt xa yb := hr.1 rfl
        wp_auto
        simp only [hi0, hiL, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index v.members' (sint.Z i) es dq ea hi0) $$ [$Hm] as Hm
        · ipureintro; exact Hea_lookup
        wp_apply (wp_slice_literal (V := fieldpath.PathElement) [ea])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_apply (wp_slice_append (V := fieldpath.PathElement) osl oes _ [ea] (DFrac.own 1)) $$ [$Hos $Hocap $Hlsl] as %osl' ⟨Hos, Hocap, -⟩
        wp_for_post
        iframe
        iexists (i + W64 1), j, osl', (oes ++ [ea]), (os ++ [xa])
        iframe
        isplitr
        · iapply (fpL.isPEL_app oes [ea] os [xa] hoel).2
          iframe Hoe; rw [fpL.isPEL_cons_eq, fpL.isPEL_nil_eq]; iframe Ha
        ipureintro
        have hi1 : (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1 := by word
        rw [hi1]
        refine ⟨by word, by word, hj0, hjm, ?_, ?_, ?_⟩
        · exact fpA.sorted_snoc_front hfr hos hsub xa
            (List.mem_append.2 (Or.inl (hxi ▸ fpA.getElem_mem_drop xs _ hixs)))
        · refine fpA.front_step_x h.1 hfr hixs ?_
          rw [hxi]
          exact fpA.lt_rest hwy h2.1 _ hjys xa (hwx xa (List.mem_of_getElem? hxa)) (hyj ▸ hlt)
        · intro x
          rw [fpA.take_succ' xs _ hixs, hxi]
          simp only [List.mem_append, List.mem_singleton, hmem]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
            · exact Or.inl (Or.inr h)
          · rintro ((h | h) | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
            · exact Or.inl (Or.inr h)
    · have hjm' := Hif
      wp_if_destruct
      · ihave %hwf := ownSlice_wf $$ Hm
        simp only [hi0, hin, hwf.2, _root_.and_self, ↓reduceIte]
        icases (ownSlice_slice i v.members'.len v.members' dq es ⟨hi0, hin, le_refl _⟩).1 $$ Hm
          with ⟨Hm1, Hmid, Hm3⟩
        wp_apply (wp_slice_append (V := fieldpath.PathElement) osl oes _ _ dq) $$ [$Hos $Hocap $Hmid]
          as %osl1 ⟨Hos, Hocap, Hmid⟩
        ihave Hm := (ownSlice_slice i v.members'.len v.members' dq es ⟨hi0, hin, le_refl _⟩).2 $$ [$Hm1 $Hmid $Hm3]
        wp_if_destruct
        · exact absurd Hif hjm'
        sorry
      · exact absurd hiL Hif
  · sorry

end proof

end smd
end EtcdGrove
end Perennial
