/-
`fieldpath.SetNodeMap.Union`: a member of the recursion cluster `fieldpath.UnionRec` (`UnionRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__UnionBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__UnionBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Less
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie

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

theorem fieldpath.SetNodeMap.Union.wp_proofBody
    (h_PathElement_Less : fieldpath.PathElement.Less.spec (GF := GF)) :
    fieldpath.SetNodeMap.Union.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.Union.specBody fieldpath.UnionRec.specI fieldpath.Set.Union.specI
    fieldpath.SetNodeMap.Union.specI
  iintro #IH
  iintro %l %l2 %D1 %D2
  wp_start as ⟨#Hn1, #Hn2⟩
  unfold isNodes
  icases Hn1 with ⟨%m1, #Hl1, Hm1⟩
  icases Hn2 with ⟨%m2, #Hl2, Hm2⟩
  icases (fpC.isNodesV_view m1 D1).1 $$ Hm1 with ⟨%ns1, %nl1, #Hns1, #Hnl1, %hok1⟩
  icases (fpC.isNodesV_view m2 D2).1 $$ Hm2 with ⟨%ns2, %nl2, #Hns2, #Hnl2, %hok2⟩
  iStructNamedSuffix Hl1 "1"
  iStructNamedSuffix Hl2 "2"
  wp_auto
  ihave %hlen1 := ownSlice_len $$ Hns1
  ihave %hlen2 := ownSlice_len $$ Hns2
  ihave %hnl1 := fpC.nodesL_length $$ Hnl1
  ihave %hnl2 := fpC.nodesL_length $$ Hnl2
  ihave %hw1 := fpC.nodesL_wf $$ Hnl1
  ihave %hw2 := fpC.nodesL_wf $$ Hnl2
  let R : Path → Prop := fun q => q ∈ fpC.nlPaths nl1 ∨ q ∈ fpC.nlPaths nl2
  ihave HI : (∃ (i j : w64) (osl : GoSlice) (outs : List fieldpath.setNode) (lo : fpC.NL),
      "i" ∷ i_ptr ↦ i ∗ "j" ∷ j_ptr ↦ j ∗
      "Ho" ∷ «$r0_ptr» ↦ (fieldpath.SetNodeMap.mk osl) ∗ "Hos" ∷ osl ↦* outs ∗
      "Hoc" ∷ ownSliceCap fieldpath.setNode osl (DFrac.own 1) ∗ "#Hlo" ∷ fpC.nodesL outs lo ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ nl1.length ∧ 0 ≤ sint.Z j ∧ sint.nat j ≤ nl2.length ∧
        fpC.Front (fpC.keys nl1) (fpC.keys nl2) (sint.nat i) (sint.nat j) ∧
        fpC.OInv nl1 nl2 (sint.nat i) (sint.nat j) lo R⌝ : IProp GF) $$ [i j «$r0»]
  · iexists W64 0, W64 0, slice.nil, [], []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    rw [fpC.nodesL_nil_eq]
    isplit
    · itrivial
    ipureintro
    have e : sint.nat (W64 0) = 0 := rfl
    rw [e]
    exact ⟨by decide, by omega, by decide, by omega, fpC.front_zero _ _, fpC.oinv_zero _ _ _⟩
  wp_for HI
  obtain ⟨hi0, hi1, hj0, hj1, hfr, hoi⟩ := Hinv
  wp_if_destruct
  · wp_if_destruct
    · rename_i Hif1
      have hi : sint.nat i < nl1.length := by rw [← hnl1, hlen1.1]; word
      have hj : sint.nat j < nl2.length := by rw [← hnl2, hlen2.1]; word
      list_elem ns1 (sint.nat i) as n1
      list_elem ns2 (sint.nat j) as n2
      icases fpC.node_at m1.members' ns1 nl1 (sint.Z i) n1 hi0 Hn1_lookup $$ [$Hns1 $Hnl1] with
        ⟨%pe1, %S1, %h1, #Hpe1f, #Hs1f, #Hpe1, #HS1⟩
      icases fpC.node_at m2.members' ns2 nl2 (sint.Z j) n2 hj0 Hn2_lookup $$ [$Hns2 $Hnl2] with
        ⟨%pe2, %S2, %h2, #Hpe2f, #Hs2f, #Hpe2, #HS2⟩
      have b1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m1.members'.len := ⟨hi0, Hif1⟩
      have b2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z m2.members'.len := ⟨hj0, Hif⟩
      simp only [b1, b2, _root_.and_self, ↓reduceIte]
      wp_auto
      simp only [b1, b2, _root_.and_self, ↓reduceIte]
      wp_pures; wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Less n1.pathElement' n2.pathElement' pe1 pe2) $$ [$Hpe1 $Hpe2] as %r %hr
      ihave %hlo := fpC.nodesL_length $$ Hlo
      have he2 : nl2[sint.nat j] = (pe2, S2) := by
        have := h2; simp only [sint.nat] at hj ⊢; rw [List.getElem?_eq_getElem hj] at this
        exact Option.some.inj this
      cases r
      · sorry
      · wp_auto
        simp only [b1, b2, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index m1.members' (sint.Z i) ns1 DFrac.discard n1 hi0) $$ [Hns1] as -
        · iframe #; ipureintro; exact Hn1_lookup
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [$Hos $Hoc $Hnsl] as %osl' ⟨Hos, Hoc, -⟩
        iapply wp_for_post_do
        wp_pures
        have he1 : nl1[sint.nat i] = (pe1, S1) := by
          have := h1; simp only [sint.nat] at hi ⊢; rw [List.getElem?_eq_getElem hi] at this
          exact Option.some.inj this
        have hlt : PE.lt nl1[sint.nat i].1 nl2[sint.nat j].1 := by
          rw [he1, he2]; exact hr.1 rfl
        obtain ⟨hf', ho'⟩ := fpC.union_step1 hok1.1 hok2.1 hfr hoi hi hj hlt
        ihave #Hlo' := fpC.nodesL_snoc outs lo n1 pe1 S1 $$ [$Hlo $Hpe1 $HS1]
        rw [he1] at ho'
        iframe
        iexists i + W64 1, j, osl', outs ++ [n1], lo ++ [(pe1, S1)]
        iframe
        isplit
        · iexact Hlo'
        ipureintro
        have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hs]
        exact ⟨by word, by omega, hj0, hj1, hf', ho'⟩
    · sorry
  · sorry

end proof

end smd
end EtcdGrove
end Perennial
