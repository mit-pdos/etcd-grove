/-
The proof of `conditionsToAppliedErroredUnevaluated.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/conditionsToAppliedErroredUnevaluated.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.conditionsToAppliedErroredUnevaluated
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsTrue
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsFalse
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsUnevaluatable
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsError
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__Error
public import Perennial.Spec.fmt.Sprintf
public import Spec.fmt.ErrorfAny
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.ForRangeB2
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B2Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem conditionsToAppliedErroredUnevaluated.wp_proof
    (wp_ConditionEvaluationResult_IsTrue : EtcdGrove.authorizer.ConditionEvaluationResult.IsTrue.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_IsFalse : EtcdGrove.authorizer.ConditionEvaluationResult.IsFalse.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_IsUnevaluatable : EtcdGrove.authorizer.ConditionEvaluationResult.IsUnevaluatable.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_IsError : EtcdGrove.authorizer.ConditionEvaluationResult.IsError.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_Error : EtcdGrove.authorizer.ConditionEvaluationResult.Error.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG)) :
    conditionsToAppliedErroredUnevaluated.spec (GF := GF) (hG := hG) := by
  intro it cs ev effect desc
  wp_start as ⟨#Hit, #Hcs, #Hev⟩
  wp_auto
  -- the state between iterations: the result cells, the accumulated errors and unevaluated
  -- conditions (owned slices), the loop variable and the parameters' cells
  let Own : IProp GF := iprop(
    (∃ (r : GoString) (e u : GoSlice), «$res0_ptr» ↦ r ∗ «$res1_ptr» ↦ e ∗ «$res2_ptr» ↦ u ∗
      (∃ el : List GoInterface, e ↦* el) ∗
      (∃ ul : List GoInterface, u ↦* ul ∗ [∗list] c ∈ ul, isCondition c)) ∗
    (∃ (es : GoSlice) (el : List GoInterface), errs_ptr ↦ es ∗ es ↦* el ∗
      ownSliceCap GoInterface es (DFrac.own 1)) ∗
    (∃ (us : GoSlice) (ul : List GoInterface), unevaluatedConditions_ptr ↦ us ∗ us ↦* ul ∗
      ownSliceCap GoInterface us (DFrac.own 1) ∗ [∗list] c ∈ ul, isCondition c) ∗
    (∃ cv : GoInterface, cond_ptr ↦ cv) ∗
    evalCond_ptr ↦ ev ∗ effect_ptr ↦ effect ∗ appliedDescription_ptr ↦ desc)
  ihave HOwn : Own $$ [«$res0» «$res1» «$res2» errs unevaluatedConditions cond evalCond effect
      appliedDescription]
  · simp only [Own]
    isplitl [«$res0» «$res1» «$res2»]
    · iexists _, _, _
      iframe
      isplitl []
      · iexists []; iapply ownSlice_nil
      · iexists []; isplitl []
        · iapply ownSlice_nil
        · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl [errs]
    · iexists _, []; iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    isplitl [unevaluatedConditions]
    · iexists _, []; iframe
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl [cond]
    · iexists _; iexact cond
    iframe
  wp_bind (App (App (Val (func.forRange 1)) _) _)
  iapply (wp_forRange_seqOk_b2 it cs _ (by rfl) (fun _ => Own) (fun _ => Own)) $$ Hit HOwn [] [HΦ]
  · iintro !> %i %x %hx HOwn
    icases HOwn with ⟨⟨%r, %e, %u, Hr0, Hr1, Hr2, He, Hu⟩, ⟨%es, %el, Herrs, Hes, Hescap⟩,
      ⟨%us, %ul, Hunev, Hus, Huscap, #Hul⟩, ⟨%cv, cond⟩, evalCond, effect, appliedDescription⟩
    ihave #Hx := BigSepL.bigSepL_lookup hx $$ Hcs
    icases isCondition_elim_b2 x $$ Hx with ⟨%ci, %Hci, #HgetID, #HgetType, #HgetCond, #HgetDesc, -⟩
    subst Hci
    ihave #HgetID' := strMethodOk_elim_b2 ci _ $$ HgetID
    ihave #HgetDesc' := strMethodOk_elim_b2 ci _ $$ HgetDesc
    ihave #Hev' := evalCondOk_elim_b2 ev (GoInterface.ok ci) $$ Hev
    wp_auto
    wp_apply HgetID' as %idv -
    wp_apply Hev' as %res -
    · iexact Hx
    wp_apply (ConditionEvaluationResult.wp_ptr_IsTrue_of_b2 wp_ConditionEvaluationResult_IsTrue
      evalResult_ptr (DFrac.own 1) res) $$ [$evalResult] as evalResult
    by_cases hT : res.resultType' = W64 1
    · simp only [hT, _root_.decide_true]
      wp_auto
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      (try wp_auto)
      wp_apply wp_Sprintf _ _ _ _ ?wf $$ [$Hargs] as %rs -
      case wf => exact .cons_string _ _ (.cons_string _ _ .nil)
      wp_apply HgetDesc' as %dv -
      wp_apply _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len dv
        as -
      by_cases hd : W64 dv.length = W64 0
      · simp only [hd, _root_.decide_true, Bool.not_true]
        wp_auto
        unfold iterBodyPost_b2
        iright
        isplitr
        · ipureintro; exact Or.inr ⟨_, rfl, isPanic_intoVal _⟩
        simp only [Own]
        isplitl [Hr0 Hr1 Hr2]
        · iexists _, _, _
          iframe
          isplitl []
          · iexists []; iapply ownSlice_nil
          · iexists []; isplitl []
            · iapply ownSlice_nil
            · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitl [Herrs Hes Hescap]
        · iexists es, el; iframe
        isplitl [Hunev Hus Huscap]
        · iexists us, ul; iframe; iexact Hul
        isplitl [cond]
        · iexists _; iexact cond
        iframe
      · simp only [hd, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        iintro %sla2 ⟨Hargs2, -⟩
        (try wp_auto)
        wp_apply wp_Sprintf _ _ _ _ ?wf2 $$ [$Hargs2] as %rs2 -
        case wf2 => exact .cons_string _ _ .nil
        unfold iterBodyPost_b2
        iright
        isplitr
        · ipureintro; exact Or.inr ⟨_, rfl, isPanic_intoVal _⟩
        simp only [Own]
        isplitl [Hr0 Hr1 Hr2]
        · iexists _, _, _
          iframe
          isplitl []
          · iexists []; iapply ownSlice_nil
          · iexists []; isplitl []
            · iapply ownSlice_nil
            · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitl [Herrs Hes Hescap]
        · iexists es, el; iframe
        isplitl [Hunev Hus Huscap]
        · iexists us, ul; iframe; iexact Hul
        isplitl [cond]
        · iexists _; iexact cond
        iframe
    · simp only [hT, _root_.decide_false]
      wp_auto
      wp_apply (ConditionEvaluationResult.wp_ptr_IsFalse_of_b2 wp_ConditionEvaluationResult_IsFalse
        evalResult_ptr (DFrac.own 1) res) $$ [$evalResult] as evalResult
      by_cases hF : res.resultType' = W64 2
      · simp only [hF, _root_.decide_true]
        wp_auto
        unfold iterBodyPost_b2
        ileft
        isplitr
        · ipureintro; exact Or.inr rfl
        simp only [Own]
        isplitl [Hr0 Hr1 Hr2 He Hu]
        · iexists r, e, u; iframe
        isplitl [Herrs Hes Hescap]
        · iexists es, el; iframe
        isplitl [Hunev Hus Huscap]
        · iexists us, ul; iframe; iexact Hul
        isplitl [cond]
        · iexists _; iexact cond
        iframe
      · simp only [hF, _root_.decide_false]
        wp_auto
        wp_apply (ConditionEvaluationResult.wp_ptr_IsUnevaluatable_of_b2
          wp_ConditionEvaluationResult_IsUnevaluatable evalResult_ptr (DFrac.own 1) res)
          $$ [$evalResult] as evalResult
        by_cases hU : res.resultType' = W64 0
        · simp only [hU, _root_.decide_true]
          wp_auto
          wp_apply wp_slice_literal
          try (isplitr; (ipureintro; rfl))
          iintro %sl1 ⟨Hsl1, -⟩
          (try wp_auto)
          wp_apply wp_slice_append $$ [$Hus $Huscap $Hsl1] as %us' ⟨Hus', Huscap', -⟩
          unfold iterBodyPost_b2
          ileft
          isplitr
          · ipureintro; exact Or.inr rfl
          simp only [Own]
          isplitl [Hr0 Hr1 Hr2 He Hu]
          · iexists r, e, u; iframe
          isplitl [Herrs Hes Hescap]
          · iexists es, el; iframe
          isplitl [Hunev Hus' Huscap']
          · iexists us', ul ++ [GoInterface.ok ci]; iframe
            iapply BigSepL.bigSepL_append.2
            isplitl []
            · iexact Hul
            · iapply BigSepL.bigSepL_singleton.2; iexact Hx
          isplitl [cond]
          · iexists _; iexact cond
          iframe
        · simp only [hU, _root_.decide_false]
          wp_auto
          wp_apply (ConditionEvaluationResult.wp_ptr_IsError_of_b2
            wp_ConditionEvaluationResult_IsError evalResult_ptr (DFrac.own 1) res)
            $$ [$evalResult] as evalResult
          by_cases hE : res.resultType' = W64 3
          · simp only [hE, _root_.decide_true]
            wp_auto
            wp_apply (ConditionEvaluationResult.wp_ptr_Error_of_b2
              wp_ConditionEvaluationResult_Error evalResult_ptr (DFrac.own 1) res)
              $$ [$evalResult] as evalResult
            (try wp_auto)
            wp_apply wp_slice_literal
            try (isplitr; (ipureintro; rfl))
            iintro %sla ⟨Hargs, -⟩
            (try wp_auto)
            wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
            · iexact Hargs
            (try wp_auto)
            wp_apply wp_slice_literal
            try (isplitr; (ipureintro; rfl))
            iintro %sle ⟨Hsle, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hes $Hescap $Hsle] as %es' ⟨Hes', Hescap', -⟩
            unfold iterBodyPost_b2
            ileft
            isplitr
            · ipureintro; exact Or.inr rfl
            simp only [Own]
            isplitl [Hr0 Hr1 Hr2 He Hu]
            · iexists r, e, u; iframe
            isplitl [Herrs Hes' Hescap']
            · iexists es', _; iframe
            isplitl [Hunev Hus Huscap]
            · iexists us, ul; iframe; iexact Hul
            isplitl [cond]
            · iexists _; iexact cond
            iframe
          · simp only [hE, _root_.decide_false]
            wp_auto
            wp_apply wp_slice_literal
            try (isplitr; (ipureintro; rfl))
            iintro %sla ⟨Hargs, -⟩
            (try wp_auto)
            wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
            · iexact Hargs
            (try wp_auto)
            wp_apply wp_slice_literal
            try (isplitr; (ipureintro; rfl))
            iintro %sle ⟨Hsle, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hes $Hescap $Hsle] as %es' ⟨Hes', Hescap', -⟩
            unfold iterBodyPost_b2
            ileft
            isplitr
            · ipureintro; exact Or.inr rfl
            simp only [Own]
            isplitl [Hr0 Hr1 Hr2 He Hu]
            · iexists r, e, u; iframe
            isplitl [Herrs Hes' Hescap']
            · iexists es', _; iframe
            isplitl [Hunev Hus Huscap]
            · iexists us, ul; iframe; iexact Hul
            isplitl [cond]
            · iexists _; iexact cond
            iframe
  · unfold iterExit_b2
    simp only [Own]
    isplit
    · iintro ⟨⟨%r, %e, %u, Hr0, Hr1, Hr2, -, -⟩, ⟨%es, %el, Herrs, Hes, -⟩,
        ⟨%us, %ul, Hunev, Hus, -, #Hul⟩, -⟩
      wp_auto
      iapply HΦ
      isplitl [Hes]
      · iexists el; iexact Hes
      · iexists ul; iframe; iexact Hul
    isplit
    · iintro ⟨⟨%r, %e, %u, Hr0, Hr1, Hr2, -, -⟩, ⟨%es, %el, Herrs, Hes, -⟩,
        ⟨%us, %ul, Hunev, Hus, -, #Hul⟩, -⟩
      wp_auto
      iapply HΦ
      isplitl [Hes]
      · iexists el; iexact Hes
      · iexists ul; iframe; iexact Hul
    · iintro %w %hw ⟨⟨%r, %e, %u, Hr0, Hr1, Hr2, He, Hu⟩, -⟩
      wp_auto
      iapply HΦ
      iframe

end proof

end authorizer
end EtcdGrove
end Perennial
