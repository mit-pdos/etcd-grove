/-
`typed.removingWalker.doList`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removingWalker__doListBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
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
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsListUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA4
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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
variable [package_sem : typed.Assumptions]

theorem typed.removingWalker.doList.wp_proofBody
    (h_MakePath : fieldpath.MakePath.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Has : fieldpath.Set.Has.spec (GF := GF))
    (h_Set_WithPrefix : fieldpath.Set.WithPrefix.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listUnstructured_RangeUsing : value.listUnstructured.RangeUsing.spec (GF := GF))
    (h_listUnstructured_RangeUsing_ptr : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (h_listUnstructuredRange_Item : value.listUnstructuredRange.Item.spec (GF := GF))
    (h_emptyRange_Item : value.emptyRange.Item.spec (GF := GF))
    (h_listUnstructuredRange_Next : value.listUnstructuredRange.Next.spec (GF := GF))
    (h_emptyRange_Next : value.emptyRange.Next.spec (GF := GF))
    (h_valueUnstructured_AsListUsing_ptr : value.valueUnstructured.AsListUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF)) :
    typed.removingWalker.doList.specBody (GF := GF) := by
  unfold typed.removingWalker.doList.specBody typed.removingWalkerRec.specI
    typed.removeItemsWithSchema.specI typed.removingWalker.doList.specI
    typed.removingWalker.doMap.specI
  iintro #IH
  icases IH with ⟨#HRm, -, -⟩
  iintro %w %sc %S %v %dq %x %rp %R %a %t %tp %e %rel %ks
  wp_start as ⟨Hown, Hv, #Hlr, %Hpre⟩
  wp_method_call; wp_call
  obtain ⟨Hfind, Hc⟩ := Hpre
  ihave ⟨Hv, %hsh⟩ := LawA3.isValF_shape _ _ _ $$ Hv
  obtain ⟨p, rfl⟩ := hsh
  unfold rmOwn
  icases Hown with ⟨Hw, #Hsc, %Hwf, #HR, Ha⟩
  icases isListRep_elim_law_holds tp e rel ks $$ Hlr with ⟨%lv, %ksl, #Hlv, %Hlv', -, #Het⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  ihave ⟨Ha, %ia, %Hia, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free a $$ [Ha]
  · iframe Ha; iPkgInit
  subst Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_valueUnstructured_IsList_ptr p dq x $$ [Hv] as %r1 ⟨Hv, %hr1⟩
  · iframe
  subst hr1
  cases hxl : x.isListB
  · wp_auto
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA4.removeAt_list_nonlist S t e rel ks R x Hfind hxl]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  obtain ⟨vs, rfl⟩ : ∃ vs, x = .list vs := by cases x <;> simp_all [UVal.isListB]
  wp_auto
  wp_apply h_valueUnstructured_AsListUsing_ptr p dq vs (GoInterface.ok ia) $$ [Hv] as %ll ⟨Hv, Hll⟩
  · iframe
  ihave ⟨HllS, HfL⟩ := (freeable_view_law_holds).2.1 _ _ $$ Hll
  ihave #Hll := isListV_persistent_law_holds ll vs $$ HllS
  try iclear HllS
  ihave ⟨%il, %Hil, #HLen, #HRange⟩ := isListV_dispatch h_listUnstructured_Length
    h_listUnstructured_Length_ptr h_listUnstructured_RangeUsing h_listUnstructured_RangeUsing_ptr ll vs $$ [Hll]
  · iframe #; iPkgInit
  subst Hil
  wp_auto
  wp_apply HLen as %nl %Hnl
  rw [show decide (nl = W64 0) = decide (vs = []) from decide_eq_decide.2 (LawB.w64_len_zero nl vs Hnl)]
  by_cases hvs : vs = []
  · simp only [hvs, decide_true]
    wp_auto
    wp_apply Hfree $$ %_ [Ha HfL] as Ha
    · iframe
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA4.removeAt_list_leaf S t e rel ks R [] Hfind (Or.inl rfl)]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  simp only [hvs, decide_false]
  wp_auto
  rw [Hlv'.1, show decide (ElemRel.goName rel = go!"atomic") = decide (rel = ElemRel.atomic) by
    simp [LawB.goName_atomic]]
  by_cases hat : rel = .atomic
  · simp only [hat, decide_true]
    wp_auto
    wp_apply Hfree $$ %_ [Ha HfL] as Ha
    · iframe
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA4.removeAt_list_leaf S t e rel ks R vs Hfind (Or.inr hat)]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  simp only [hat, decide_false]
  obtain ⟨hassoc, hksnd, fs, em, rel', hfe, -⟩ := LawB.list_wf S Hwf t e rel ks Hfind hat
  subst hassoc
  wp_auto
  wp_apply HRange $$ %_ [Ha] as %r1 ⟨Ha, Hr1⟩
  · iexact Ha
  ihave ⟨Hr1, %i1, %Hi1, #HR1⟩ := ownRange_dispatch h_listUnstructuredRange_Item h_emptyRange_Item
    h_listUnstructuredRange_Next h_emptyRange_Next r1 vs (-1) $$ [Hr1]
  · iframe; iPkgInit
  subst Hi1
  iunfold rangeIfaceM at HR1
  icases HR1 with ⟨#HN1, #HI1⟩
  ihave Hns0 := ownSlice_nil (V := GoInterface) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := GoInterface) (GF := GF)
  ihave HI : (∃ (n : Int) (ns : GoSlice) (xs : List GoInterface),
      "Hr1" ∷ ownRange (GoInterface.ok i1) vs n ∗
      "newItems" ∷ newItems_ptr ↦ ns ∗ "Hns" ∷ ns ↦* xs ∗
      "Hcap" ∷ ownSliceCap GoInterface ns (DFrac.own 1) ∗
      "#Hxs" ∷ □ (∀ q : GoInterface × UVal,
        ⌜q ∈ xs.zip (removeL S e ks R (vs.take (n + 1).toNat))⌝ -∗ isIface q.1 q.2) ∗
      "Ha" ∷ isAlloc (GoInterface.ok ia) ∗
      "%Hn" ∷ ⌜-1 ≤ n ∧ n < vs.length ∧
        xs.length = (removeL S e ks R (vs.take (n + 1).toNat)).length⌝ : IProp GF)
    $$ [Hr1 newItems Hns0 Hcap0 Ha]
  · iexists (-1), slice.nil, []
    iframe Hr1 newItems Ha
    isplitl [Hns0]
    · iexact Hns0
    isplitl [Hcap0]
    · iexact Hcap0
    isplitr
    · imodintro; iintro %q %hq; simp at hq
    ipureintro
    refine ⟨by omega, by have : vs.length ≠ 0 := by simpa using hvs
                         omega, by simp [removeL]⟩
  wp_for HI
  wp_apply HN1 $$ %vs %n [Hr1] as %b1 ⟨Hr1, %Hb1⟩
  · iframe; ipureintro; exact Hn.2.1
  cases b1
  · cleanup_bool_decide
    wp_auto
    have hend : (n + 1).toNat = vs.length := by
      have := Hb1; simp at this; omega
    have hT : removeL S e ks R (List.take (n + 1).toNat vs) = removeL S e ks R vs := by
      rw [hend, List.take_of_length_le (Nat.le_refl _)]
    rw [hT] at Hn
    irevert Hxs; rw [hT]; iintro #Hxs
    ihave %Hnsl := ownSlice_len _ _ _ $$ Hns
    rw [LawA4.removeAt_list_items S t e .associative ks R vs Hfind hvs hat]
    by_cases hL : removeL S e ks R vs = []
    · have h0 : decide (sint.Z (W64 0) < sint.Z ns.len) = false := by
        have : xs.length = 0 := by rw [Hn.2.2, hL]; rfl
        simp only [decide_eq_false_iff_not]; have := Hnsl.1; have := Hnsl.2; word
      rw [h0]
      wp_auto
      wp_apply Hfree $$ %_ [Ha Hr1] as Ha
      · iframe; iapply (ownRange_freeable_law_holds _ vs _); iexact Hr1
      wp_apply Hfree $$ %_ [Ha HfL] as Ha
      · iframe
      iapply HΦ
      iexists GoInterface.nil
      iframe; iframe #
      rw [if_pos hL]
      isplitr
      · ipureintro; exact Hwf
      iapply (isIface_scalar_law_holds (GF := GF)).1
      ipureintro; trivial
    · have h0 : decide (sint.Z (W64 0) < sint.Z ns.len) = true := by
        have : xs.length ≠ 0 := by rw [Hn.2.2]; simpa using hL
        simp only [decide_eq_true_eq]; have := Hnsl.1; have := Hnsl.2; word
      rw [h0]
      imod ownSlice_persist _ _ _ $$ Hns with #Hns
      wp_auto
      wp_apply Hfree $$ %_ [Ha Hr1] as Ha
      · iframe; iapply (ownRange_freeable_law_holds _ vs _); iexact Hr1
      wp_apply Hfree $$ %_ [Ha HfL] as Ha
      · iframe
      iapply HΦ
      iexists _
      iframe; iframe #
      rw [if_neg hL]
      isplitr
      · ipureintro; exact Hwf
      iapply isIface_list_law_holds ns xs _ Hn.2.2 $$ Hns
      iapply LawA3.sepL_of_forall
      iexact Hxs
  · rw [if_pos (by simp)]
    wp_auto
    have hlt : (n + 1).toNat < vs.length := by simp at Hb1; omega
    list_elem vs (n + 1).toNat as xi
    wp_apply HI1 $$ %vs %(n + 1) %xi [Hr1] as %j1 %item ⟨%Hj1, Hit, Hback⟩
    · iframe; ipureintro; exact ⟨by omega, Hxi_lookup⟩
    try wp_auto
    obtain ⟨hall, hassoc⟩ := conforms_item_law_holds S t e .associative ks vs Hfind Hc
    obtain ⟨hks, -⟩ := hassoc rfl
    have hxin : xi ∈ vs := List.mem_of_getElem? Hxi_lookup
    have hcx := hall xi hxin
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks xi).isSome from hks xi hxin)
    have hkne : ks ≠ [] := by rintro rfl; simp [keyOf] at hk; split at hk <;> simp_all
    wp_apply h_listItemToPathElement (GoInterface.ok ia) sc S tp e ks fs em rel' item (DFrac.own 1) xi t.name
      $$ [Ha Hit] as %pe1 %err Hpost
    · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, Hfind, hcx, by rw [hk]; rfl⟩
    rw [hk]
    icases Hpost with ⟨Ha, Hit, %herr, #Hpe1⟩
    subst herr
    try wp_auto
    wp_apply (wp_slice_literal (V := GoInterface) [interface.mkOk fieldpath.PathElement.ty #pe1])
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    ihave #Hpes : isPEs (GF := GF) [pe1] [k] $$ []
    · iapply (isPEs_cons_law_holds pe1 [] k []).2
      iframe #
      iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
      ipureintro; trivial
    wp_apply h_MakePath _ (DFrac.own 1) [interface.mkOk fieldpath.PathElement.ty #pe1] [pe1] [k]
      $$ [Hsl1] as %fp %err2 ⟨%herr2, Hsl1, Hfp⟩
    · iframe; iframe #; ipureintro; rfl
    subst herr2
    try wp_auto
    wp_apply h_Set_Has rp R fp (DFrac.own 1) [k] $$ [Hfp] as %hm ⟨Hfp, %Hhm⟩
    · iframe #; iframe
    try wp_auto
    wp_apply h_Set_WithPrefix rp R pe1 k $$ [] as %rp2 #Hrp2
    · iframe #
    wp_apply h_Set_Empty rp2 (R.under k) $$ [] as %emp %Hemp
    · iframe #
    try wp_auto
    have hn1 : (n + 1 + 1).toNat = (n + 1).toNat + 1 := by omega
    have hsucc := LawA4.removeL_take_succ S e ks R vs (n + 1).toNat xi Hxi_lookup
    cases hm
    · have hnin : [k] ∉ R := fun h => by simpa using Hhm.2 h
      wp_auto
      cases emp
      · have hne : ¬ (R.under k).IsEmpty := fun h => by simpa using Hemp.2 h
        have hstep : LawA4.removeStep S e ks R xi = [removeAt S e (R.under k) xi] := by
          simp [LawA4.removeStep, hk, hnin, hne]
        wp_auto
        wp_apply h_Set_WithPrefix rp R pe1 k $$ [] as %rp3 #Hrp3
        · iframe #
        try wp_auto
        wp_func_call
        wp_apply HRm $$ %item %(DFrac.own 1) %xi %rp3 %sc %(R.under k) %S %lv.ElementType' %e [Hit]
          as %v' ⟨Hit, Hv'⟩
        · iframe; iframe #; ipureintro; exact ⟨Hwf, hcx⟩
        try wp_auto
        ispecialize Hback $$ Hit
        ihave ⟨Hy, %hsh'⟩ := LawA3.isValF_shape _ _ _ $$ Hv'
        obtain ⟨p', rfl⟩ := hsh'
        wp_apply h_valueUnstructured_Unstructured_ptr p' _ (removeAt S e (R.under k) xi) $$ [Hy] as %u ⟨Hy, #Hu⟩
        · iframe
        wp_apply (wp_slice_literal (V := GoInterface) [u])
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply (wp_slice_append (V := GoInterface) ns xs _ [u] (DFrac.own 1)) $$ [Hns Hcap Hsl2]
          as %ns' ⟨Hns', Hcap', -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists (n + 1), ns', xs ++ [u]
        iframe
        rw [hn1, hsucc, hstep]
        isplitr
        · imodintro
          iintro %q %hq
          rw [List.zip_append Hn.2.2] at hq
          rcases List.mem_append.1 hq with hq | hq
          · iapply Hxs; ipureintro; exact hq
          · simp at hq; subst hq; iexact Hu
        ipureintro
        refine ⟨by omega, by simp at Hb1; omega, by simp [Hn.2.2]⟩
      · have he : (R.under k).IsEmpty := Hemp.1 rfl
        have hstep : LawA4.removeStep S e ks R xi = [xi] := by
          simp [LawA4.removeStep, hk, hnin, he]
        wp_auto
        ihave ⟨Hy, %hsh'⟩ := LawA3.isValF_shape _ _ _ $$ Hit
        obtain ⟨p', rfl⟩ := hsh'
        wp_apply h_valueUnstructured_Unstructured_ptr p' _ xi $$ [Hy] as %u ⟨Hy, #Hu⟩
        · iframe
        ispecialize Hback $$ Hy
        wp_apply (wp_slice_literal (V := GoInterface) [u])
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply (wp_slice_append (V := GoInterface) ns xs _ [u] (DFrac.own 1)) $$ [Hns Hcap Hsl2]
          as %ns' ⟨Hns', Hcap', -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists (n + 1), ns', xs ++ [u]
        iframe
        rw [hn1, hsucc, hstep]
        isplitr
        · imodintro
          iintro %q %hq
          rw [List.zip_append Hn.2.2] at hq
          rcases List.mem_append.1 hq with hq | hq
          · iapply Hxs; ipureintro; exact hq
          · simp at hq; subst hq; iexact Hu
        ipureintro
        refine ⟨by omega, by simp at Hb1; omega, by simp [Hn.2.2]⟩
    · ispecialize Hback $$ Hit
      have hin : [k] ∈ R := Hhm.1 rfl
      have hstep : LawA4.removeStep S e ks R xi = [] := by
        simp [LawA4.removeStep, hk, hin]
      wp_auto
      wp_for_post
      iframe
      iexists (n + 1), ns, xs
      iframe
      rw [hn1, hsucc, hstep, List.append_nil]
      iframe #
      ipureintro
      refine ⟨by omega, by simp at Hb1; omega, Hn.2.2⟩

end proof

end smd
end EtcdGrove
end Perennial
