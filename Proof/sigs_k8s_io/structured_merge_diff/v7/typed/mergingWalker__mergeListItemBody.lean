/-
`typed.mergingWalker.mergeListItem`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__mergeListItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__prepareDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
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

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.mergingWalker.mergeListItem.wp_proofBody
    (h_mergingWalker_finishDescent : typed.mergingWalker.finishDescent.spec (GF := GF))
    (h_mergingWalker_prepareDescent : typed.mergingWalker.prepareDescent.spec (GF := GF)) :
    typed.mergingWalker.mergeListItem.specBody (GF := GF) := by
  unfold typed.mergingWalker.mergeListItem.specBody typed.mergingWalkerRec.specI
    typed.mergingWalker.merge.specI typed.mergingWalker.doList.specI
    typed.mergingWalker.doMap.specI typed.mergingWalker.mergeListItem.specI
    typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI
    typed.mergingWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %tp %e %rel %ks %pe %pe' %lc %rc %dql %dqr %l %r %sp
  wp_start as ⟨Hown, #Hl, #Hpe, Hlc, Hrc, %Hpre⟩
  icases IH with ⟨-, -, #Hmerge, -⟩
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha⟩
  icases isListRep_elim_law_holds tp e rel ks $$ Hl with ⟨%lv, %ksl, #Hlv, %Hlv', -, #Het⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  wp_auto
  wp_apply h_mergingWalker_prepareDescent w sc S st ps sp st.alloc pe pe' lv.ElementType' e
    $$ [Hcore Hp Hsp] as %w2 ⟨%sp1, %ps2, Hcore, Hcore2, Hp2, Hsp, %Hsp1⟩
  · iframe; iframe #
  iunfold mwCore at Hcore2
  icases Hcore2 with ⟨%tr2, %rule2, %o2, Hw2, #Htr2, #Hsc2, %Hwf2, #Hrule2, #Ho2⟩
  wp_auto
  ihave Hown2 : mwOwn w2 sc S (MWSt.mk lc rc e (st.path ++ [pe']) none st.inLeaf st.alloc) sp1
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
  by_cases ho : o3 = null
  · rw [decide_eq_true ho]
    subst ho
    wp_auto
    wp_apply h_mergingWalker_finishDescent w w2 sc S st
        (MWSt.mk lc rc e (st.path ++ [pe']) (mergeO S e l r) (leafAt S e l r) st.alloc) ps ps3 sp1 st.alloc pe'
      $$ [Hcore Hw2 Hp3 Hsp] as ⟨%ps4, Hcore, Hp, Hsp⟩
    · iframe
      isplitl [Hw2]
      · unfold mwCore
        iexists tr3, rule3, null
        iframe
        iframe #
        ipureintro; exact Hwf3
      ipureintro; exact Hsp1.1
    try wp_auto
    iapply HΦ
    iframe
    isplitl
    · iexists sp1
      isplitl; rotate_left
      · ipureintro; exact Hsp1.2
      unfold mwOwn
      iexists ps4
      iframe
    iframe #
  · rw [decide_eq_false ho]
    wp_auto
    wp_apply h_mergingWalker_finishDescent w w2 sc S st
        (MWSt.mk lc rc e (st.path ++ [pe']) (mergeO S e l r) (leafAt S e l r) st.alloc) ps ps3 sp1 st.alloc pe'
      $$ [Hcore Hw2 Hp3 Hsp] as ⟨%ps4, Hcore, Hp, Hsp⟩
    · iframe
      isplitl [Hw2]
      · unfold mwCore
        iexists tr3, rule3, o3
        iframe
        iframe #
        ipureintro; exact Hwf3
      ipureintro; exact Hsp1.1
    try wp_auto
    iapply HΦ
    iframe
    isplitl
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
