/-
`value.ListCompareUsing`: a member of the recursion cluster `value.CompareUsingRec` (`CompareUsingRec.lean`); its proof is the
projection of the cluster's (its body is `ListCompareUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListCompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Next
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Next
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCompare
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCmp
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

theorem value.ListCompareUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_RangeUsing : value.listUnstructured.RangeUsing.spec (GF := GF))
    (h_listUnstructured_RangeUsing_ptr : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (h_listUnstructuredRange_Item : value.listUnstructuredRange.Item.spec (GF := GF))
    (h_emptyRange_Item : value.emptyRange.Item.spec (GF := GF))
    (h_listUnstructuredRange_Next : value.listUnstructuredRange.Next.spec (GF := GF))
    (h_emptyRange_Next : value.emptyRange.Next.spec (GF := GF)) :
    value.ListCompareUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.ListCompareUsing.specI
  iintro %al %l %r %xs %ys
  wp_start as ⟨Ha, #Hl, #Hr, %Hok⟩
  iunfold value.CompareUsingRec.specI at IH
  icases IH with ⟨#HC, -, -⟩
  iunfold value.CompareUsing.specI at HC
  ihave ⟨%il, %Hil, #HlRange⟩ := isListV_rangeDispatch
    h_listUnstructured_RangeUsing h_listUnstructured_RangeUsing_ptr l xs $$ [Hl]
  · isplitr; iexact Hpkg; iexact Hl
  ihave ⟨%ir, %Hir, #HrRange⟩ := isListV_rangeDispatch
    h_listUnstructured_RangeUsing h_listUnstructured_RangeUsing_ptr r ys $$ [Hr]
  · isplitr; iexact Hpkg; iexact Hr
  ihave ⟨Ha, %ia, %Hia, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
  · iframe; iexact Hpkg
  subst Hil Hir Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply HlRange $$ %_ [Ha] as %r1 ⟨Ha, Hr1⟩
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
  ihave HI : (∃ n : Int, "Hr1" ∷ ownRange (.ok i1) xs n ∗ "Hr2" ∷ ownRange (.ok i2) ys n ∗
      "Ha" ∷ isAlloc (.ok ia) ∗
      "%Hn" ∷ ⌜-1 ≤ n ∧ n < xs.length ∧ n < ys.length ∧
        ValueCompare.listCmp UVal.compare xs ys =
          ValueCompare.listCmp UVal.compare (xs.drop (n + 1).toNat) (ys.drop (n + 1).toNat)⌝ : IProp GF)
    $$ [Hr1 Hr2 Ha]
  · iexists (-1)
    iframe
    ipureintro
    refine ⟨by omega, by omega, by omega, by simp⟩
  wp_for HI
  wp_apply HN1 $$ %xs %n [Hr1] as %b1 ⟨Hr1, %Hb1⟩
  · iframe; ipureintro; exact Hn.2.1
  wp_apply HN2 $$ %ys %n [Hr2] as %b2 ⟨Hr2, %Hb2⟩
  · iframe; ipureintro; exact Hn.2.2.1
  have hd1 : ∀ m : Int, -1 ≤ m → ¬ (m < xs.length) → List.drop m.toNat xs = [] := by
    intro m hm h; apply List.drop_eq_nil_of_le; omega
  have hd2 : ∀ m : Int, -1 ≤ m → ¬ (m < ys.length) → List.drop m.toNat ys = [] := by
    intro m hm h; apply List.drop_eq_nil_of_le; omega
  cases b1 <;> cases b2 <;> wp_auto
  · -- both ended
    have e1 := hd1 (n + 1) (by omega) (of_decide_eq_false Hb1.symm)
    have e2 := hd2 (n + 1) (by omega) (of_decide_eq_false Hb2.symm)
    wp_for_post
    wp_apply HFree $$ %(GoInterface.ok i2) [Ha Hr2] as Ha
    · iframe; iapply (ownRange_freeable_law_holds _ ys _); iexact Hr2
    wp_apply HFree $$ %(GoInterface.ok i1) [Ha Hr1] as Ha
    · iframe; iapply (ownRange_freeable_law_holds _ xs _); iexact Hr1
    iapply HΦ; iframe; ipureintro
    rw [ValueCompare.compare_list, Hn.2.2.2, e1, e2]; rfl
  · -- the left one ended
    have e1 := hd1 (n + 1) (by omega) (of_decide_eq_false Hb1.symm)
    have h2 := of_decide_eq_true Hb2.symm
    obtain ⟨y, ys', e2⟩ : ∃ y ys', List.drop (n + 1).toNat ys = y :: ys' := by
      cases h : List.drop (n + 1).toNat ys with
      | nil => rw [List.drop_eq_nil_iff] at h; omega
      | cons y ys' => exact ⟨y, ys', rfl⟩
    wp_for_post
    wp_apply HFree $$ %(GoInterface.ok i2) [Ha Hr2] as Ha
    · iframe; iapply (ownRange_freeable_law_holds _ ys _); iexact Hr2
    wp_apply HFree $$ %(GoInterface.ok i1) [Ha Hr1] as Ha
    · iframe; iapply (ownRange_freeable_law_holds _ xs _); iexact Hr1
    iapply HΦ; iframe; ipureintro
    rw [ValueCompare.compare_list, Hn.2.2.2, e1, e2]; rfl
  · -- the right one ended
    have e2 := hd2 (n + 1) (by omega) (of_decide_eq_false Hb2.symm)
    have h1 := of_decide_eq_true Hb1.symm
    obtain ⟨x, xs', e1⟩ : ∃ x xs', List.drop (n + 1).toNat xs = x :: xs' := by
      cases h : List.drop (n + 1).toNat xs with
      | nil => rw [List.drop_eq_nil_iff] at h; omega
      | cons x xs' => exact ⟨x, xs', rfl⟩
    wp_for_post
    wp_apply HFree $$ %(GoInterface.ok i2) [Ha Hr2] as Ha
    · iframe; iapply (ownRange_freeable_law_holds _ ys _); iexact Hr2
    wp_apply HFree $$ %(GoInterface.ok i1) [Ha Hr1] as Ha
    · iframe; iapply (ownRange_freeable_law_holds _ xs _); iexact Hr1
    iapply HΦ; iframe; ipureintro
    rw [ValueCompare.compare_list, Hn.2.2.2, e1, e2]; rfl
  · -- both have an item
    have h1 := of_decide_eq_true Hb1.symm
    have h2 := of_decide_eq_true Hb2.symm
    list_elem xs (n + 1).toNat as x
    list_elem ys (n + 1).toNat as y
    wp_apply HI1 $$ %xs %(n + 1) %x [Hr1] as %j1 %lv ⟨%Hj1, Hlv, Hback1⟩
    · iframe; ipureintro; exact ⟨by omega, Hx_lookup⟩
    wp_apply HI2 $$ %ys %(n + 1) %y [Hr2] as %j2 %rv ⟨%Hj2, Hrv, Hback2⟩
    · iframe; ipureintro; exact ⟨by omega, Hy_lookup⟩
    wp_apply HC $$ %(GoInterface.ok ia) %lv %rv %(DFrac.own 1) %(DFrac.own 1) %x %y [Ha Hlv Hrv]
      as %c ⟨Ha, Hlv, Hrv, %Hc⟩
    · iframe; ipureintro
      exact ⟨ValueCmp.mapLensOkL_mem (List.mem_of_getElem? Hx_lookup) (by simpa [UVal.mapLensOk] using Hok.1),
        ValueCmp.mapLensOkL_mem (List.mem_of_getElem? Hy_lookup) (by simpa [UVal.mapLensOk] using Hok.2)⟩
    ispecialize Hback1 $$ Hlv
    ispecialize Hback2 $$ Hrv
    have ex : xs.drop (n + 1).toNat = x :: xs.drop ((n + 1).toNat + 1) := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 Hx_lookup
      rw [List.drop_eq_getElem_cons hlt, heq]
    have ey : ys.drop (n + 1).toNat = y :: ys.drop ((n + 1).toNat + 1) := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 Hy_lookup
      rw [List.drop_eq_getElem_cons hlt, heq]
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (n + 1)
      iframe
      ipureintro
      refine ⟨by omega, by omega, by omega, ?_⟩
      rw [Hn.2.2.2, ex, ey, show (n + 1 + 1).toNat = (n + 1).toNat + 1 by omega]
      simp only [ValueCompare.listCmp]
      rw [← Hc]; simp
    · wp_for_post
      wp_apply HFree $$ %(GoInterface.ok i2) [Ha Hback2] as Ha
      · iframe; iapply (ownRange_freeable_law_holds _ ys _); iexact Hback2
      wp_apply HFree $$ %(GoInterface.ok i1) [Ha Hback1] as Ha
      · iframe; iapply (ownRange_freeable_law_holds _ xs _); iexact Hback1
      iapply HΦ; iframe; ipureintro
      have hc0 : x.compare y ≠ 0 := by
        rw [← Hc]; intro h; apply Hif; apply BitVec.eq_of_toInt_eq; simpa using h
      rw [ValueCompare.compare_list, Hn.2.2.2, ex, ey]
      simp only [ValueCompare.listCmp, hc0, ↓reduceIte]; exact Hc

end proof

end smd
end EtcdGrove
end Perennial
