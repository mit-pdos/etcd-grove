/-
`typed.validatingObjectWalker.validate`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__validateBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validateBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doScalar

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
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

theorem typed.validatingObjectWalker.validate.wp_proofBody
    (h_ValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (h_resolveSchema : typed.resolveSchema.spec (GF := GF))
    (h_validatingObjectWalker_doScalar : typed.validatingObjectWalker.doScalar.spec (GF := GF)) :
    typed.validatingObjectWalker.validate.specBody (GF := GF) := by
  unfold typed.validatingObjectWalker.validate.specBody typed.validatingObjectWalkerRec.specI
    typed.validatingObjectWalker.validate.specI typed.validatingObjectWalker.doList.specI
    typed.validatingObjectWalker.doMap.specI typed.validatingObjectWalker.visitListItems.specI
    typed.validatingObjectWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %dq %x %f
  wp_start as ⟨Hown, Hv, %Hfind, %Hc⟩
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 Hfind
  iunfold vwOwn at Hown
  icases Hown with ⟨%sp, Hcore, Hsp, Ha⟩
  iunfold vwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  wp_auto
  ihave Hown : vwOwn w sc S st $$ [Hw Hsp Ha]
  · unfold vwOwn vwCore
    iexists sp
    iframe Hsp Ha
    iexists tr
    iframe Hw
    iframe #
    ipureintro; exact Hwf
  icases IH with ⟨#HdL, #HdM, -, -, -⟩
  wp_apply h_resolveSchema sc S tr st.t A st.value dq (some x)
    (go.GoType.PointerType typed.validatingObjectWalker.ty) #w iprop(vwOwn w sc S st)
    (fun errs => iprop(noErrs errs ∗ isValO st.value dq (some x) ∗ vwOwn w sc S st))
    $$ [Hv Hown] as %errs ⟨Herrs, Hv, Hown⟩
  · iframe #
    unfold isValO
    iframe Hv Hown
    isplitr
    · ipureintro; exact ⟨Hwf, hA⟩
    iintro %atm #Hat
    cases A with
    | scalar s =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_scalar_law_holds atm s).1 $$ Hat with ⟨#Hs, -⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply h_validatingObjectWalker_doScalar w sc S st dq x atm.Scalar' s $$ [Hv Hown]
        as %errs ⟨Herrs, Hv, Hown⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc⟩
      iapply HΦ2
      iframe
    | list e rel ks =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_list_law_holds atm e rel ks).1 $$ Hat with ⟨-, #Hl⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply HdL $$ [Hv Hown] as %errs ⟨Herrs, Hv, Hown⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc⟩
      iapply HΦ2
      iframe
    | map fs e rel =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_map_law_holds atm fs e rel).1 $$ Hat with ⟨-, #Hm⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply HdM $$ [Hv Hown] as %errs ⟨Herrs, Hv, Hown⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc⟩
      iapply HΦ2
      iframe
  iunfold noErrs at Herrs
  iunfold ownErrs at Herrs
  icases Herrs with ⟨Hes, Hcap⟩
  wp_apply h_ValidationErrors_WithLazyPrefix errs [] f $$ [Hes] as ⟨%es', Hes, %hl⟩
  · iframe Hes; ileft; ipureintro; rfl
  have he : es' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
  subst he
  try wp_auto
  iapply HΦ
  unfold isValO
  iframe Hv Hown
  unfold noErrs ownErrs
  iframe

end proof

end smd
end EtcdGrove
end Perennial
