/-
`fieldpath.SetNodeMap.Difference`: a member of the recursion cluster `fieldpath.DifferenceRec` (`DifferenceRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__DifferenceBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__DifferenceBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Less
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsMerge

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

theorem fieldpath.SetNodeMap.Difference.wp_proofBody
    (h_PathElement_Less : fieldpath.PathElement.Less.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF)) :
    fieldpath.SetNodeMap.Difference.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.Difference.specBody fieldpath.DifferenceRec.specI fieldpath.Set.Difference.specI
    fieldpath.SetNodeMap.Difference.specI
  iintro #IH
  iintro %l %p2 %D1 %B
  wp_start as ⟨#Hn1, #Hs2⟩
  unfold isNodes
  icases Hn1 with ⟨%m1, #Hl1, Hm1⟩
  icases (fpC.isSet_view p2 B).1 $$ Hs2 with ⟨%v2, #Hp2, #Hpm2, #Hm2, %hne2⟩
  icases (fpC.isNodesV_view m1 D1).1 $$ Hm1 with ⟨%ns1, %nl1, #Hns1, #Hnl1, %hok1⟩
  icases (fpC.isNodesV_view v2.Children' B.deep).1 $$ Hm2 with ⟨%ns2, %nl2, #Hns2, #Hnl2, %hok2⟩
  iStructNamedSuffix Hl1 "1"
  iStructNamedSuffix Hp2 "2"
  iStructNamedSuffix Children2 "c"
  wp_auto
  ihave %hlen1 := ownSlice_len $$ Hns1
  ihave %hlen2 := ownSlice_len $$ Hns2
  ihave %hnl1 := fpC.nodesL_length $$ Hnl1
  ihave %hnl2 := fpC.nodesL_length $$ Hnl2
  ihave %hw1 := fpC.nodesL_wf $$ Hnl1
  ihave %hw2 := fpC.nodesL_wf $$ Hnl2
  let R : Path → Prop := fpC.RD nl1 nl2
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
  iapply wp_fupd
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
      icases fpC.node_at v2.Children'.members' ns2 nl2 (sint.Z j) n2 hj0 Hn2_lookup $$ [$Hns2 $Hnl2] with
        ⟨%pe2, %S2, %h2, #Hpe2f, #Hs2f, #Hpe2, #HS2⟩
      have b1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m1.members'.len := ⟨hi0, Hif1⟩
      have b2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v2.Children'.members'.len := ⟨hj0, Hif⟩
      simp only [b1, b2, _root_.and_self, ↓reduceIte]
      wp_auto
      simp only [b1, b2, _root_.and_self, ↓reduceIte]
      wp_pures; wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Less n1.pathElement' n2.pathElement' pe1 pe2) $$ [$Hpe1 $Hpe2] as %r %hr
      ihave %hlo := fpC.nodesL_length $$ Hlo
      have he1 : nl1[sint.nat i] = (pe1, S1) := by
        have := h1; simp only [sint.nat] at hi ⊢; rw [List.getElem?_eq_getElem hi] at this
        exact Option.some.inj this
      have he2 : nl2[sint.nat j] = (pe2, S2) := by
        have := h2; simp only [sint.nat] at hj ⊢; rw [List.getElem?_eq_getElem hj] at this
        exact Option.some.inj this
      cases r
      · wp_auto
        repeat (simp only [b1, b2, _root_.and_self, ↓reduceIte]; wp_auto)
        try simp only [b1, b2, _root_.and_self, ↓reduceIte]
        wp_pures; wp_method_call; wp_call; wp_auto
        wp_apply (h_PathElement_Less n2.pathElement' n1.pathElement' pe2 pe1) $$ [$Hpe1 $Hpe2] as %r2 %hr2
        have hw1' : pe1.wf = true := hw1 pe1 S1 (by rw [← he1]; exact List.getElem_mem hi)
        have hw2' : pe2.wf = true := hw2 pe2 S2 (by rw [← he2]; exact List.getElem_mem hj)
        cases r2
        · have heq : pe1 = pe2 := by
            rcases fpC.lt_total hw1' hw2' with h | h | h
            · exact absurd (hr.2 h) (by simp)
            · exact h
            · exact absurd (hr2.2 h) (by simp)
          have he : nl1[sint.nat i].1 = nl2[sint.nat j].1 := by rw [he1, he2]; exact heq
          obtain ⟨hf', hadd, hskip⟩ := fpC.diff_step12 hok1.1 hok2.1 hfr hoi hi hj he
          rw [he1, he2] at hadd hskip
          wp_auto
          repeat (simp only [b1, b2, _root_.and_self, ↓reduceIte]; wp_auto)
          try simp only [b1, b2, _root_.and_self, ↓reduceIte]
          icases IH with ⟨#HI, -⟩
          wp_apply HI $$ %n1.set' %n2.set' %S1 %S2 [] as %p #Hp
          · iframe #
          wp_apply h_Set_Empty $$ [$Hp] as %b %hb
          have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
          have hs2 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          cases b
          · have hne : ∃ r, r ∈ PathSet.diff S1 S2 := by
              refine Classical.byContradiction fun hc => ?_
              exact absurd (hb.2 ((fpC.isEmpty_iff _).2 (fun r h => hc ⟨r, h⟩))) (by simp)
            have ho' := hadd hne
            wp_auto
            repeat (simp only [b1, b2, _root_.and_self, ↓reduceIte]; wp_auto)
            try simp only [b1, b2, _root_.and_self, ↓reduceIte]
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %nsl ⟨Hnsl, -⟩
            wp_auto
            wp_apply wp_slice_append $$ [$Hos $Hoc $Hnsl] as %osl' ⟨Hos, Hoc, -⟩
            wp_for_post
            ihave #Hlo' := fpC.nodesL_snoc outs lo ⟨n1.pathElement', p⟩ pe1 (PathSet.diff S1 S2)
              $$ [$Hlo $Hpe1 $Hp]
            iframe
            iexists i + W64 1, j + W64 1, osl', outs ++ [⟨n1.pathElement', p⟩],
              lo ++ [(pe1, PathSet.diff S1 S2)]
            iframe
            isplit
            · iexact Hlo'
            ipureintro
            rw [hs, hs2]
            exact ⟨by word, by omega, by word, by omega, hf', ho'⟩
          · have hemp : ∀ r, r ∉ PathSet.diff S1 S2 := (fpC.isEmpty_iff _).1 (hb.1 rfl)
            have ho' := hskip hemp
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, j + W64 1, osl, outs, lo
            iframe
            isplit
            · iexact Hlo
            ipureintro
            rw [hs, hs2]
            exact ⟨by word, by omega, by word, by omega, hf', ho'⟩
        · have hlt : PE.lt nl2[sint.nat j].1 nl1[sint.nat i].1 := by
            rw [he1, he2]; exact hr2.1 rfl
          obtain ⟨hf', ho'⟩ := fpC.diff_step2 hok1.1 hok2.1 hfr hoi hi hj hlt
          wp_auto
          wp_for_post
          iframe
          iexists i, j + W64 1, osl, outs, lo
          iframe
          isplit
          · iexact Hlo
          ipureintro
          rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
          exact ⟨hi0, hi1, by word, by omega, hf', ho'⟩
      · have hlt : PE.lt nl1[sint.nat i].1 nl2[sint.nat j].1 := by
          rw [he1, he2]; exact hr.1 rfl
        obtain ⟨hf', ho'⟩ := fpC.diff_step1 hok1.1 hok2.1 hfr hoi hi hj hlt
        rw [he1] at ho'
        wp_auto
        repeat (simp only [b1, b2, _root_.and_self, ↓reduceIte]; wp_auto)
        try simp only [b1, b2, _root_.and_self, ↓reduceIte]
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [$Hos $Hoc $Hnsl] as %osl' ⟨Hos, Hoc, -⟩
        wp_for_post
        ihave #Hlo' := fpC.nodesL_snoc outs lo ⟨n1.pathElement', n1.set'⟩ pe1 S1
          $$ [$Hlo $Hpe1 $HS1]
        iframe
        iexists i + W64 1, j, osl', outs ++ [⟨n1.pathElement', n1.set'⟩], lo ++ [(pe1, S1)]
        iframe
        isplit
        · iexact Hlo'
        ipureintro
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
        exact ⟨by word, by omega, hj0, hj1, hf', ho'⟩
    · -- `s2`'s children consumed: the rest of `s` appended
      rename_i Hif1
      have hjn := Hif
      have hjl : sint.nat j = nl2.length := by rw [← hnl2, hlen2.1]; word
      have hin : sint.Z i ≤ sint.Z m1.members'.len := by word
      rw [hjl] at hfr hoi
      wp_if_destruct
      · ihave %hwf := ownSlice_wf $$ Hns1
        simp only [hi0, hin, hwf.2, _root_.and_self, ↓reduceIte]
        icases (ownSlice_slice i m1.members'.len m1.members' DFrac.discard ns1
          ⟨hi0, hin, Int.le_refl _⟩).1 $$ Hns1 with ⟨-, Hmid, -⟩
        wp_apply (wp_slice_append (V := fieldpath.setNode) osl outs _ _ DFrac.discard)
          $$ [$Hos $Hoc $Hmid] as %osl1 ⟨Hos, Hoc, -⟩
        have hsl : subslice (sint.nat i) (sint.nat m1.members'.len) ns1 = ns1.drop (sint.nat i) := by
          unfold subslice; rw [List.take_of_length_le (Nat.le_of_eq hlen1.1)]
        rw [hsl]
        ipersist Ho
        ihave #Hd := fpC.nodesL_drop ns1 nl1 (sint.nat i) $$ Hnl1
        ihave #Ho2 := fpC.nodesL_append outs (ns1.drop (sint.nat i)) lo (nl1.drop (sint.nat i)) $$ [$Hlo $Hd]
        have hfin := fpC.diff_tail1 hok1.1 hi1 hfr hoi
        ipersist Hos
        imodintro
        iapply HΦ
        iexists _
        isplit
        · iexact Ho
        iapply (fpC.isNodesV_view _ _).2
        iexists (outs ++ ns1.drop (sint.nat i)), (lo ++ nl1.drop (sint.nat i))
        isplit
        · iexact Hos
        isplit
        · iexact Ho2
        ipureintro
        exact ⟨hfin.1, fpC.diff_final hok1.1 hfin D1 B hok1.2 hok2.2⟩
      · exact absurd Hif1 Hif
  · have hil : sint.nat i = nl1.length := by rw [← hnl1, hlen1.1]; word
    have hin := Hif
    rw [hil] at hoi
    wp_if_destruct
    · exact absurd Hif hin
    ipersist Ho
    ipersist Hos
    imodintro
    iapply HΦ
    iexists _
    isplit
    · iexact Ho
    iapply (fpC.isNodesV_view _ _).2
    iexists outs, lo
    isplit
    · iexact Hos
    isplit
    · iexact Hlo
    ipureintro
    exact ⟨hoi.1, fpC.diff_final hok1.1 hoi D1 B hok1.2 hok2.2⟩

end proof

end smd
end EtcdGrove
end Perennial
