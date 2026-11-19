/-
`value.ListEqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `ListEqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListEqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Next
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Next
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsRec

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
variable [package_sem : value.Assumptions]

theorem value.ListEqualsUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listUnstructured_RangeUsing : value.listUnstructured.RangeUsing.spec (GF := GF))
    (h_listUnstructured_RangeUsing_ptr : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (h_listUnstructuredRange_Item : value.listUnstructuredRange.Item.spec (GF := GF))
    (h_emptyRange_Item : value.emptyRange.Item.spec (GF := GF))
    (h_listUnstructuredRange_Next : value.listUnstructuredRange.Next.spec (GF := GF))
    (h_emptyRange_Next : value.emptyRange.Next.spec (GF := GF)) :
    value.ListEqualsUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.ListEqualsUsing.specI
  iintro %al %l %r %xs %ys
  wp_start as ⟨Ha, #Hl, #Hr⟩
  iunfold value.EqualsUsingRec.specI at IH
  icases IH with ⟨#HEq, -, -, -, -⟩
  iunfold value.EqualsUsing.specI at HEq
  ihave ⟨%il, %Hil, #HlLen, #HlRange⟩ := isListV_dispatch h_listUnstructured_Length
    h_listUnstructured_Length_ptr h_listUnstructured_RangeUsing h_listUnstructured_RangeUsing_ptr l xs $$ [Hl]
  · isplitr; iexact Hpkg; iexact Hl
  ihave ⟨%ir, %Hir, #HrLen, #HrRange⟩ := isListV_dispatch h_listUnstructured_Length
    h_listUnstructured_Length_ptr h_listUnstructured_RangeUsing h_listUnstructured_RangeUsing_ptr r ys $$ [Hr]
  · isplitr; iexact Hpkg; iexact Hr
  ihave ⟨Ha, %ia, %Hia, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
  · iframe; iexact Hpkg
  subst Hil Hir Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply HlLen as %nl %Hnl
  wp_apply HrLen as %nr %Hnr
  wp_if_destruct
  · wp_apply HlRange $$ %_ [Ha] as %r1 ⟨Ha, Hr1⟩
    · iexact Ha
    ihave ⟨Hr1, %i1, %Hi1, #HR1⟩ := ownRange_dispatch h_listUnstructuredRange_Item h_emptyRange_Item
      h_listUnstructuredRange_Next h_emptyRange_Next r1 xs (-1) $$ [Hr1]
    · iframe; iexact Hpkg
    subst Hi1
    wp_apply HrRange $$ %_ [Ha] as %r2 ⟨Ha, Hr2⟩
    · iexact Ha
    ihave ⟨Hr2, %i2, %Hi2, #HR2⟩ := ownRange_dispatch h_listUnstructuredRange_Item h_emptyRange_Item
      h_listUnstructuredRange_Next h_emptyRange_Next r2 ys (-1) $$ [Hr2]
    · iframe; iexact Hpkg
    subst Hi2
    iunfold rangeIfaceM at HR1 HR2
    icases HR1 with ⟨#HN1, #HI1⟩
    icases HR2 with ⟨#HN2, #HI2⟩
    have hlen : xs.length = ys.length := by
      subst Hif; omega
    ihave HI : (∃ n : Int, "Hr1" ∷ ownRange (.ok i1) xs n ∗ "Hr2" ∷ ownRange (.ok i2) ys n ∗
        "Ha" ∷ isAlloc (.ok ia) ∗
        "%Hn" ∷ ⌜-1 ≤ n ∧ n < xs.length ∧ xs.take (n + 1).toNat = ys.take (n + 1).toNat⌝ : IProp GF)
      $$ [Hr1 Hr2 Ha]
    · iexists (-1)
      iframe
      ipureintro
      refine ⟨by omega, by omega, by simp⟩
    wp_for HI
    wp_apply HN1 $$ %xs %n [Hr1] as %b1 ⟨Hr1, %Hb1⟩
    · iexact Hr1
    cases b1
    · wp_auto
      cleanup_bool_decide
      wp_auto
      wp_apply HFree $$ %(GoInterface.ok i2) [Ha Hr2] as Ha
      · iframe; iapply (ownRange_freeable_law_holds _ ys _); iexact Hr2
      wp_apply HFree $$ %(GoInterface.ok i1) [Ha Hr1] as Ha
      · iframe; iapply (ownRange_freeable_law_holds _ xs _); iexact Hr1
      iapply HΦ
      iframe
      ipureintro
      simp only [true_iff]
      have h1 : (n + 1).toNat = xs.length := by
        have := Hb1; simp at this; omega
      have hx := Hn.2.2
      rw [h1, List.take_of_length_le (Nat.le_refl _), hlen, List.take_of_length_le (Nat.le_refl _)] at hx
      exact hx
    · wp_auto
      wp_apply HN2 $$ %ys %n [Hr2] as %b2 ⟨Hr2, %Hb2⟩
      · iexact Hr2
      have hb2 : b2 = true := by subst Hb2; simp at Hb1 ⊢; omega
      subst hb2
      cleanup_bool_decide
      wp_auto
      have hlt : (n + 1).toNat < xs.length := by simp at Hb1; omega
      list_elem xs (n + 1).toNat as x
      list_elem ys (n + 1).toNat as y
      wp_apply HI1 $$ %xs %(n + 1) %x [Hr1] as %j1 %lv ⟨%Hj1, Hlv, Hback1⟩
      · iframe; ipureintro; exact ⟨by omega, Hx_lookup⟩
      wp_apply HI2 $$ %ys %(n + 1) %y [Hr2] as %j2 %rv ⟨%Hj2, Hrv, Hback2⟩
      · iframe; ipureintro; exact ⟨by omega, Hy_lookup⟩
      wp_apply HEq $$ %(GoInterface.ok ia) %lv %rv %(DFrac.own 1) %(DFrac.own 1) %x %y [Ha Hlv Hrv]
        as %r ⟨Ha, Hlv, Hrv, %Hxy⟩
      · iframe
      ispecialize Hback1 $$ Hlv
      ispecialize Hback2 $$ Hrv
      cases r
      · wp_auto
        wp_for_post
        wp_apply HFree $$ %(GoInterface.ok i2) [Ha Hback2] as Ha
        · iframe; iapply (ownRange_freeable_law_holds _ ys _); iexact Hback2
        wp_apply HFree $$ %(GoInterface.ok i1) [Ha Hback1] as Ha
        · iframe; iapply (ownRange_freeable_law_holds _ xs _); iexact Hback1
        iapply HΦ
        iframe
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        intro h; subst h
        rw [Hx_lookup] at Hy_lookup; cases Hy_lookup
        simp at Hxy
      · wp_auto
        wp_for_post
        iframe
        iexists (n + 1)
        iframe
        ipureintro
        refine ⟨by omega, by simp at Hb1; omega, ?_⟩
        rw [show (n + 1 + 1).toNat = (n + 1).toNat + 1 by omega,
          ValuePure.take_succ_of_getElem? xs _ x Hx_lookup,
          ValuePure.take_succ_of_getElem? ys _ y Hy_lookup, Hn.2.2, (Hxy.1 rfl)]
  · iapply HΦ
    iframe
    ipureintro
    constructor
    · intro h; cases h
    · intro h; subst h; exact absurd (by apply BitVec.eq_of_toInt_eq; omega) Hif

end proof

end smd
end EtcdGrove
end Perennial
