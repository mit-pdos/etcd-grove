/-
`typed.mergingWalker.visitMapItem`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__visitMapItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__prepareDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

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

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.mergingWalker.visitMapItem.wp_proofBody
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_mergingWalker_finishDescent : typed.mergingWalker.finishDescent.spec (GF := GF))
    (h_mergingWalker_prepareDescent : typed.mergingWalker.prepareDescent.spec (GF := GF)) :
    typed.mergingWalker.visitMapItem.specBody (GF := GF) := by
  unfold typed.mergingWalker.visitMapItem.specBody typed.mergingWalkerRec.specI
    typed.mergingWalker.merge.specI typed.mergingWalker.doList.specI
    typed.mergingWalker.doMap.specI typed.mergingWalker.mergeListItem.specI
    typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI
    typed.mergingWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %tp %fs %e %rel %om %M %key %t' %lc %rc %dql %dqr %l %r %sp
  wp_start as ⟨Hown, #Hm, Hom, Hlc, Hrc, %Hpre⟩
  obtain ⟨Hnd, Hft, Hpre⟩ := Hpre
  icases IH with ⟨-, -, #Hmerge, -⟩
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha⟩
  icases isMapRep_elim_law_holds tp fs e rel $$ Hm with
    ⟨%fsl, %sfs, %etv, -, -, -, -, -, #Het, #Hetv, -⟩
  wp_auto
  wp_apply h_Map_FindField tp fs e rel key $$ [] as %sf %ok Hsf
  · iframe #; ipureintro; exact Hnd
  wp_join iprop(∃ tr : schema.TypeRef, fieldType_ptr ↦ tr ∗ isTypeRef tr t')
    at (if: _ then _ else _) with [fieldType Hsf sf] as ⟨%tr, fieldType, #Htrt⟩
  · rcases hl : lookupKV key fs with _ | t
    · simp only [hl]
      icases Hsf with %Hsf
      obtain ⟨rfl, rfl⟩ := Hsf
      have he : e = some t' := by simpa [fieldType, hl] using Hft
      subst he
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists etv
      iframe
      iapply (isTypeRefOpt_some_law_holds etv t').1 $$ Hetv
    · simp only [hl]
      icases Hsf with ⟨%Hok, Hsf⟩
      subst Hok
      icases (isStructField_elim_law_holds sf (key, t)).1 $$ Hsf with ⟨%-, #Ht⟩
      have ht : t = t' := by simpa [fieldType, hl] using Hft
      subst ht
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists sf.Type'
      iframe
      iexact Ht
  ipersist key
  ihave #Hpe := isPE_field_intro { FieldName' := key_ptr, Key' := null, Value' := null, Index' := null } key $$ key
  wp_apply h_mergingWalker_prepareDescent w sc S st ps sp st.alloc _ (.field key) tr t'
    $$ [Hcore Hp Hsp] as %w2 ⟨%sp1, %ps2, Hcore, Hcore2, Hp2, Hsp, %Hsp1⟩
  · iframe; iframe #
  iunfold mwCore at Hcore2
  icases Hcore2 with ⟨%tr2, %rule2, %o2, Hw2, #Htr2, #Hsc2, %Hwf2, #Hrule2, #Ho2⟩
  wp_auto
  ihave Hown2 : mwOwn w2 sc S (MWSt.mk lc rc t' (st.path ++ [.field key]) none st.inLeaf st.alloc) sp1
      $$ [Hw2 Hp2 Hsp Ha]
  · unfold mwOwn mwCore
    iexists ps2
    iframe
    simp only
    iframe #
    ipureintro; exact Hwf2
  wp_apply Hmerge $$ [Hown2 Hlc Hrc] as %errs ⟨Herrs, Hlc, Hrc, %sp2, Hown2, %Hsp2⟩
  · iframe
    ipureintro
    exact ⟨Hpre.1, Hpre.2.1, Hpre.2.2.1, rfl, Hpre.2.2.2⟩
  rw [show sp2 = sp1 from Hsp2 Hsp1.1]
  simp only
  iunfold mwOwn at Hown2
  icases Hown2 with ⟨%ps3, Hcore3, Hp3, Hsp, Ha⟩
  iunfold mwCore at Hcore3
  icases Hcore3 with ⟨%tr3, %rule3, %o3, Hw2, #Htr3, #Hsc3, %Hwf3, #Hrule3, #Ho3⟩
  simp only [noErrs, ownErrs]
  icases Herrs with ⟨Herrs, Hcap⟩
  wp_apply (wp_slice_append (V := typed.ValidationError) slice.nil [] errs [] (DFrac.own 1))
    $$ [Herrs] as %e2 ⟨He2, Hcap2, -⟩
  · iframe
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  try wp_auto
  cases hm : mergeO S t' l r with
  | none =>
    simp only [hm, outRep]
    icases Ho3 with %ho
    subst ho
    wp_auto
    wp_apply h_mergingWalker_finishDescent w w2 sc S st
        (MWSt.mk lc rc t' (st.path ++ [.field key]) none (leafAt S t' l r) st.alloc) ps ps3 sp1 st.alloc (.field key)
      $$ [Hcore Hw2 Hp3 Hsp] as ⟨%ps4, Hcore, Hp, Hsp⟩
    · iframe
      isplitl [Hw2]
      · unfold mwCore
        iexists tr3, rule3, null
        iframe
        iframe #
        simp only [outRep]
        isplit
        · ipureintro; exact Hwf3
        · ipureintro; simp
      ipureintro; exact Hsp1.1
    try wp_auto
    iapply HΦ
    iframe
    iexists sp1
    isplitl; rotate_left
    · ipureintro; exact Hsp1.2
    unfold mwOwn
    iexists ps4
    iframe
  | some x =>
    simp only [hm, outRep]
    icases Ho3 with ⟨%i, #Hoi, #Hi⟩
    ihave ⟨Hoi2, %Honn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hoi
    rw [decide_eq_false Honn]
    wp_auto
    wp_apply wp_mapInsert $$ Hom as Hom
    try wp_auto
    wp_apply h_mergingWalker_finishDescent w w2 sc S st
        (MWSt.mk lc rc t' (st.path ++ [.field key]) (some x) (leafAt S t' l r) st.alloc) ps ps3 sp1 st.alloc (.field key)
      $$ [Hcore Hw2 Hp3 Hsp] as ⟨%ps4, Hcore, Hp, Hsp⟩
    · iframe
      isplitl [Hw2]
      · unfold mwCore
        iexists tr3, rule3, o3
        iframe
        iframe #
        simp only [outRep]
        isplit
        · ipureintro; exact Hwf3
        · iexists i; iframe #
      ipureintro; exact Hsp1.1
    try wp_auto
    iapply HΦ
    iframe
    isplitl [Hcore Hp Hsp Ha]
    · iexists sp1
      isplitl; rotate_left
      · ipureintro; exact Hsp1.2
      unfold mwOwn
      iexists ps4
      iframe
    iframe #

end proof

end smd
end EtcdGrove
end Perennial
