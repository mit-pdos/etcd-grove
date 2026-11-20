/-
`typed.toFieldSetWalker.toFieldSet`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__toFieldSetBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSetBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doScalar
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
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

theorem typed.toFieldSetWalker.toFieldSet.wp_proofBody
    (h_resolveSchema : typed.resolveSchema.spec (GF := GF))
    (h_toFieldSetWalker_doScalar : typed.toFieldSetWalker.doScalar.spec (GF := GF)) :
    typed.toFieldSetWalker.toFieldSet.specBody (GF := GF) := by
  unfold typed.toFieldSetWalker.toFieldSet.specBody typed.toFieldSetWalkerRec.specI
    typed.toFieldSetWalker.toFieldSet.specI typed.toFieldSetWalker.doList.specI
    typed.toFieldSetWalker.doMap.specI typed.toFieldSetWalker.visitListItems.specI
    typed.toFieldSetWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %s %F %dq %x
  wp_start as ⟨Hown, Hv, %Hpre⟩
  obtain ⟨Hc, Hcard⟩ := Hpre
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 (LawA.conforms_find S st.t x Hc)
  iunfold twOwn at Hown
  icases Hown with ⟨%ps, %sp, Hcore, Hps, Hsp, Ha, Hs⟩
  iunfold twCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  wp_auto
  ihave Hown : twOwn w sc S st s F $$ [Hw Hps Hsp Ha Hs]
  · unfold twOwn twCore
    iexists ps, sp
    iframe
    iframe #
    ipureintro; exact Hwf
  icases IH with ⟨#HdL, #HdM, -, -, -⟩
  wp_apply h_resolveSchema sc S tr st.t A st.value dq (some x)
    (go.GoType.PointerType typed.toFieldSetWalker.ty) #w iprop(twOwn w sc S st s F)
    (fun errs => iprop(noErrs errs ∗ isValO st.value dq (some x) ∗
      twOwn w sc S st s (F.union (fieldsAt S st.t st.path x))))
    $$ [Hv Hown] as %errs ⟨Herrs, Hv, Hown⟩
  · iframe #
    unfold isValO
    iframe Hv Hown
    isplitr
    · ipureintro; exact ⟨Hwf, hA⟩
    iintro %atm #Hat
    cases A with
    | scalar s' =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_scalar_law_holds atm s').1 $$ Hat with ⟨#Hs', -⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply h_toFieldSetWalker_doScalar w sc S st s F dq x atm.Scalar' $$ [Hv Hown]
        as %errs ⟨Herrs, Hv, Hown⟩
      · iframe #; iframe; ipureintro; exact ⟨⟨s', hA⟩, Hc, Hcard⟩
      iapply HΦ2
      iframe
    | list e rel ks =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_list_law_holds atm e rel ks).1 $$ Hat with ⟨-, #Hl⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply HdL $$ [Hv Hown] as %errs ⟨Herrs, Hv, Hown⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc, Hcard⟩
      iapply HΦ2
      iframe
    | map fs e rel =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_map_law_holds atm fs e rel).1 $$ Hat with ⟨-, #Hm⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply HdM $$ [Hv Hown] as %errs ⟨Herrs, Hv, Hown⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc, Hcard⟩
      iapply HΦ2
      iframe
  try wp_auto
  iapply HΦ
  unfold isValO
  iframe

end proof

end smd
end EtcdGrove
end Perennial
