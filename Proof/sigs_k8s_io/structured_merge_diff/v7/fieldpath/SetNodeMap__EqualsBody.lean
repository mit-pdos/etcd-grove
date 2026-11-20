/-
`fieldpath.SetNodeMap.Equals`: a member of the recursion cluster `fieldpath.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EqualsBody
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals

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

theorem fieldpath.SetNodeMap.Equals.wp_proofBody
    (h_PathElement_Equals : fieldpath.PathElement.Equals.spec (GF := GF)) :
    fieldpath.SetNodeMap.Equals.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.Equals.specBody fieldpath.EqualsRec.specI
    fieldpath.Set.Equals.specI fieldpath.SetNodeMap.Equals.specI
  iintro #IH
  iintro %l %l2 %D1 %D2
  wp_start as ⟨#Hn1, #Hn2⟩
  unfold isNodes
  icases Hn1 with ⟨%m1, #Hm1, Hv1⟩
  icases Hn2 with ⟨%m2, #Hm2, Hv2⟩
  icases (fpC.isNodesV_view m1 D1).1 $$ Hv1 with ⟨%ns1, %nl1, #Hns1, #Hl1, %hok1⟩
  icases (fpC.isNodesV_view m2 D2).1 $$ Hv2 with ⟨%ns2, %nl2, #Hns2, #Hl2, %hok2⟩
  have hD1 : D1 = fpC.nlPaths nl1 := FSet.ext' hok1.2
  have hD2 : D2 = fpC.nlPaths nl2 := FSet.ext' hok2.2
  subst hD1 hD2
  have heq : fpC.nlPaths nl1 = fpC.nlPaths nl2 ↔ nl1 = nl2 :=
    ⟨fpK.nl_eq_of hok1.1 hok2.1, fun h => h ▸ rfl⟩
  rw [heq]
  ihave %hlen1 := fpC.nodesL_length ns1 nl1 $$ Hl1
  ihave %hlen2 := fpC.nodesL_length ns2 nl2 $$ Hl2
  ihave %hsl1 := ownSlice_len $$ Hns1
  ihave %hsl2 := ownSlice_len $$ Hns2
  iStructNamedSuffix Hm1 "1"
  iStructNamedSuffix Hm2 "2"
  wp_auto
  wp_if_destruct
  · have Hlq := Hif
    rename_i iv_ptr
    irename : (iv_ptr ↦ zero_val w64 : IProp GF) => Hiv
    have hlen : nl1.length = nl2.length := by
      have : sint.nat m1.members'.len = sint.nat m2.members'.len := by rw [Hif]
      omega
    ihave HL : iprop(∃ (k x : w64), "i" ∷ i_ptr ↦ k ∗ "Hiv" ∷ iv_ptr ↦ x ∗
        "%hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z m1.members'.len ∧
          nl1.take (sint.nat k) = nl2.take (sint.nat k)⌝) $$ [i Hiv]
    · iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word, rfl⟩
    wp_for HL
    wp_if_destruct
    · have Hif' : sint.Z k < sint.Z m1.members'.len := by simpa [intoVal_eq_iff] using Hif
      have Hif2 : sint.Z k < sint.Z m2.members'.len := by rw [← Hlq]; exact Hif'
      rw [if_pos ⟨hk.1, Hif'⟩]
      have hk1 : sint.nat k < ns1.length := by word
      have hk2 : sint.nat k < ns2.length := by rw [hsl2.1, ← Hlq]; word
      list_elem ns1 (sint.nat k) as n1
      list_elem ns2 (sint.nat k) as n2
      wp_apply (wp_load_slice_index m1.members' (sint.Z k) ns1 DFrac.discard n1 hk.1) $$ [$Hns1] as _
      · ipureintro; exact Hn1_lookup
      icases fpC.node_at m1.members' ns1 nl1 (sint.Z k) n1 hk.1 Hn1_lookup $$ [$Hns1 $Hl1] with
        ⟨%pe1, %S1, %h1, #Hpe1f, #Hs1f, #Hpe1, #HS1⟩
      icases fpC.node_at m2.members' ns2 nl2 (sint.Z k) n2 hk.1 Hn2_lookup $$ [$Hns2 $Hl2] with
        ⟨%pe2, %S2, %h2, #Hpe2f, #Hs2f, #Hpe2, #HS2⟩
      have b1 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z m1.members'.len := ⟨hk.1, Hif'⟩
      have b2 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z m2.members'.len := ⟨hk.1, Hif2⟩
      simp only [b1, b2, _root_.and_self, ↓reduceIte]
      wp_auto
      simp only [b1, b2, _root_.and_self, ↓reduceIte]
      wp_pures; wp_method_call; wp_call; wp_auto
      wp_apply (h_PathElement_Equals n1.pathElement' n2.pathElement' pe1 pe2) $$ [$Hpe1 $Hpe2] as %r %hr
      have hkl1 : sint.nat k < nl1.length := by omega
      have hkl2 : sint.nat k < nl2.length := by omega
      have he1 : nl1[sint.nat k] = (pe1, S1) := by
        have := h1; simp only [sint.nat] at hkl1 ⊢; rw [List.getElem?_eq_getElem hkl1] at this
        exact Option.some.inj this
      have he2 : nl2[sint.nat k] = (pe2, S2) := by
        have := h2; simp only [sint.nat] at hkl2 ⊢; rw [List.getElem?_eq_getElem hkl2] at this
        exact Option.some.inj this
      cases r
      · wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        intro h; subst h
        have : pe1 = pe2 := by
          have := he1.symm.trans he2; exact (Prod.mk.inj this).1
        exact absurd (hr.2 this) (by simp)
      · have hpe : pe1 = pe2 := hr.1 rfl
        wp_auto
        simp only [b1, b2, _root_.and_self, ↓reduceIte]
        wp_auto
        simp only [b1, b2, _root_.and_self, ↓reduceIte]
        wp_auto
        icases IH with ⟨#HSe, -⟩
        wp_apply HSe $$ %n1.set' %n2.set' %S1 %S2 [] as %b %hb
        · iframe #
        cases b
        · wp_auto
          wp_for_post
          iapply HΦ
          ipureintro
          simp only [Bool.false_eq_true, false_iff]
          intro h; subst h
          have : S1 = S2 := by
            have := he1.symm.trans he2; exact (Prod.mk.inj this).2
          exact absurd (hb.2 this) (by simp)
        · have hS : S1 = S2 := hb.1 rfl
          wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, _
          iframe
          ipureintro
          rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, fpC.take_succ' nl1 _ hkl1,
            fpC.take_succ' nl2 _ hkl2, hk.2.2, he1, he2, hpe, hS]
          exact ⟨by word, by word, rfl⟩
    · iapply HΦ
      ipureintro
      simp only [_root_.true_iff]
      have hk1 : sint.nat k = nl1.length := by word
      have hk2 : sint.nat k = nl2.length := by omega
      have := hk.2.2
      rw [hk1, List.take_length, ← hk1, hk2, List.take_length] at this
      exact this
  · iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff]
    intro h; subst h
    apply Hif
    have : sint.nat m1.members'.len = sint.nat m2.members'.len := by omega
    word

end proof

end smd
end EtcdGrove
end Perennial
