/-
`typed.compareWalker.compareListItem`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__compareListItemBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__prepareDescent
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
theorem typed.compareWalker.compareListItem.wp_proofBody
    (h_compareWalker_finishDescent : typed.compareWalker.finishDescent.spec (GF := GF))
    (h_compareWalker_prepareDescent : typed.compareWalker.prepareDescent.spec (GF := GF)) :
    typed.compareWalker.compareListItem.specBody (GF := GF) := by
  unfold typed.compareWalker.compareListItem.specBody typed.compareWalkerRec.specI
    typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI
    typed.compareWalker.doList.specI typed.compareWalker.doMap.specI
    typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI
    typed.compareWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %c %C %tp %e %rel %ks %pe %pe' %lc %rc %dql %dqr %l %r %sp
  wp_start as ⟨Hown, #Hl, #Hpe, Hlc, Hrc, %Hpre⟩
  icases IH with ⟨#Hcmp, -⟩
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha, Hc⟩
  icases isListRep_elim_law_holds tp e rel ks $$ Hl with ⟨%lv, %ksl, #Hlv, %Hlv', -, #Het⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc0, %Hwf0⟩
  wp_auto
  wp_apply h_compareWalker_prepareDescent w sc S st ps c sp st.alloc pe pe' lv.ElementType' e c
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
  ihave Hown2 : cwOwn w2 sc S (CWSt.mk lc rc e (st.path ++ [pe']) st.inLeaf st.alloc) c C sp1
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
    exact ⟨Hpre.1, Hpre.2.1, Hpre.2.2.1, Hpre.2.2.2.1, Hpre.2.2.2.2⟩
  rw [show sp2 = sp1 from Hsp2 Hsp1.1]
  simp only
  iunfold cwOwn at Hown2
  icases Hown2 with ⟨%ps3, Hcore3, Hp3, Hsp, Ha, Hc⟩
  wp_auto
  wp_apply h_compareWalker_finishDescent w w2 sc S st
    (CWSt.mk lc rc e (st.path ++ [pe']) (leafAt S e l r) st.alloc) ps ps3 c c sp1 st.alloc pe'
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
