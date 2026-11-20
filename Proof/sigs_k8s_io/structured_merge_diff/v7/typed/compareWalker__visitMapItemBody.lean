/-
`typed.compareWalker.visitMapItem`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__visitMapItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__prepareDescent
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
theorem typed.compareWalker.visitMapItem.wp_proofBody
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_compareWalker_finishDescent : typed.compareWalker.finishDescent.spec (GF := GF))
    (h_compareWalker_prepareDescent : typed.compareWalker.prepareDescent.spec (GF := GF)) :
    typed.compareWalker.visitMapItem.specBody (GF := GF) := by
  unfold typed.compareWalker.visitMapItem.specBody typed.compareWalkerRec.specI
    typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI
    typed.compareWalker.doList.specI typed.compareWalker.doMap.specI
    typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI
    typed.compareWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %c %C %tp %fs %e %rel %om %key %t' %lc %rc %dql %dqr %l %r %sp
  wp_start as ⟨Hown, #Hm, Hlc, Hrc, %Hpre⟩
  obtain ⟨Hnd, Hft, Hpre⟩ := Hpre
  icases IH with ⟨#Hcmp, -⟩
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha, Hc⟩
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc0, %Hwf0⟩
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
  wp_apply h_compareWalker_prepareDescent w sc S st ps c sp st.alloc _ (.field key) tr t' c
    $$ [Hw Hp Hsp] as %w2 ⟨%sp1, %ps2, Hcore, Hcore2, Hp2, Hsp, %Hsp1⟩
  · iframe; iframe #
    unfold cwCore
    iexists tr0
    iframe
    iframe #
    ipureintro; exact Hwf0
  iunfold cwCore at Hcore2
  icases Hcore2 with ⟨%tr2, Hw2, #Htr2, #Hsc2, %Hwf2⟩
  wp_auto
  ihave Hown2 : cwOwn w2 sc S (CWSt.mk lc rc t' (st.path ++ [.field key]) st.inLeaf st.alloc) c C sp1
      $$ [Hw2 Hp2 Hsp Ha Hc]
  · unfold cwOwn cwCore
    iexists ps2
    iframe
    simp only
    iframe #
    ipureintro; exact Hwf2
  wp_apply Hcmp $$ [Hown2 Hlc Hrc] as %errs ⟨Herrs, Hlc, Hrc, %sp2, Hown2, %Hsp2⟩
  · iframe
    ipureintro
    exact Hpre
  rw [show sp2 = sp1 from Hsp2 Hsp1.1]
  simp only
  iunfold cwOwn at Hown2
  icases Hown2 with ⟨%ps3, Hcore3, Hp3, Hsp, Ha, Hc⟩
  simp only [noErrs, ownErrs]
  icases Herrs with ⟨Herrs, Hcap⟩
  wp_apply (wp_slice_append (V := typed.ValidationError) slice.nil [] errs [] (DFrac.own 1))
    $$ [Herrs] as %e2 ⟨He2, Hcap2, -⟩
  · iframe
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  try wp_auto
  wp_apply h_compareWalker_finishDescent w w2 sc S st
    (CWSt.mk lc rc t' (st.path ++ [.field key]) (leafAt S t' l r) st.alloc) ps ps3 c c sp1 st.alloc (.field key)
    $$ [Hcore Hcore3 Hp3 Hsp] as ⟨%ps4, Hcore, Hp, Hsp⟩
  · iframe
    ipureintro; exact Hsp1.1
  try wp_auto
  iapply HΦ
  iframe
  iexists sp1
  isplitl; rotate_left
  · ipureintro; exact Hsp1.2
  unfold cwOwn
  iexists ps4
  iframe

end proof

end smd
end EtcdGrove
end Perennial
