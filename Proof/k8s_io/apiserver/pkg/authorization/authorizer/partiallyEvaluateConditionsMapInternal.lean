/-
The proof of `partiallyEvaluateConditionsMapInternal.spec` (`Spec/k8s_io/apiserver/pkg/authorizati
on/authorizer/partiallyEvaluateConditionsMapInternal.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.partiallyEvaluateConditionsMapInternal
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsUnevaluatable
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__DenyConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.conditionsToAppliedErroredUnevaluated
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__NoOpinionConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__AllowConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B2Lemmas
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer
open _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem partiallyEvaluateConditionsMapInternal.wp_proof
    (wp_ConditionEvaluationResult_IsUnevaluatable : EtcdGrove.authorizer.ConditionEvaluationResult.IsUnevaluatable.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_DenyConditions : EtcdGrove.authorizer.ConditionsMap.DenyConditions.spec (GF := GF) (hG := hG))
    (wp_conditionsToAppliedErroredUnevaluated : EtcdGrove.authorizer.conditionsToAppliedErroredUnevaluated.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecisionConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_NoOpinionConditions : EtcdGrove.authorizer.ConditionsMap.NoOpinionConditions.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_AllowConditions : EtcdGrove.authorizer.ConditionsMap.AllowConditions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG)) :
    partiallyEvaluateConditionsMapInternal.spec (GF := GF) (hG := hG) := by
  intro ctx c dn no al data f
  wp_start as ⟨#Hc, #Hf⟩
  wp_auto
  ipersist ctx
  ipersist data
  ipersist evaluateConditionFn
  icases pointsto_name_b2 evalCond_ptr _ $$ evalCond with ⟨%ev, evalCond, %hev⟩
  -- the closure `evalCond` can be called on any condition
  ihave #Hev : evalCondOk ev $$ []
  · subst hev
    unfold evalCondOk evalCondCallOk
    iintro %cond !> %Ψ #Hcond HΨ
    ihave #Hcond2 := isCondition_elim_b2 cond $$ Hcond
    icases Hcond2 with ⟨%ci, %Hci, -, -, -, -, #Heval⟩
    subst Hci
    ihave #HevC := condEvalOk_elim_b2 ci ctx data $$ (Heval $$ %ctx %data)
    wp_auto
    wp_apply HevC as %r #Hr
    wp_apply (ConditionEvaluationResult.wp_ptr_IsUnevaluatable_of_b2
      wp_ConditionEvaluationResult_IsUnevaluatable result_ptr (DFrac.own 1) r) $$ [$result] as result
    by_cases hU : r.resultType' = W64 0
    · simp only [hU, _root_.decide_true]
      wp_auto
      by_cases hfn : f = func.nil
      · simp only [hfn, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΨ
        iexact Hr
      · simp only [hfn, _root_.decide_false, Bool.not_false]
        wp_auto
        ihave Hf2 := maybeEvalFnOk_elim_b2 f $$ Hf
        icases Hf2 with (%hnil | #Hcall)
        · exact absurd hnil hfn
        ihave #Hcall' := maybeEvalCallOk_elim_b2 f ctx (GoInterface.ok ci) data $$ (Hcall $$ %ctx %(GoInterface.ok ci) %data)
        wp_apply Hcall' as %r' #Hr'
        · iexact Hcond
        iapply HΨ
        iexact Hr'
    · simp only [hU, _root_.decide_false]
      wp_auto
      iapply HΨ
      iexact Hr
  unfold isConditionsMap condsOk
  icases Hc with ⟨⟨#Hsd, #Hdn⟩, ⟨#Hsn, #Hno⟩, ⟨#Hsa, #Hal⟩⟩
  by_cases h00 : c.denyConditions'.len = W64 0
  · simp only [h00, _root_.decide_true, Bool.not_true]
    wp_auto
    by_cases h10 : c.noOpinionConditions'.len = W64 0
    · simp only [h10, _root_.decide_true, Bool.not_true]
      wp_auto
      by_cases h20 : c.allowConditions'.len = W64 0
      · simp only [h20, _root_.decide_true, Bool.not_true]
        wp_auto
        wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
        · first | iassumption | iapply utilerrors.errTreeOrNil_nil
        (try wp_auto)
        iapply HΦ
        unfold isWFDecisionLe
        iexists .noOpinion
        isplitr
        · iexact Hd
        · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
      simp only [h20, _root_.decide_false, Bool.not_false]
      wp_auto
      wp_apply (ConditionsMap.wp_ptr_AllowConditions_of_b2 wp_ConditionsMap_AllowConditions c_ptr
        (DFrac.own 1) c al) $$ [$c] as %it ⟨c, #Hit⟩
      · iexact Hsa
      (try wp_auto)
      wp_apply (wp_conditionsToAppliedErroredUnevaluated it al ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_string_len r as -
      by_cases hr : W64 r.length = W64 0
      · simp only [hr, _root_.decide_true, Bool.not_true]
        wp_auto
        by_cases he : es.len = W64 0
        · simp only [he, _root_.decide_true, Bool.not_true]
          wp_auto
          by_cases hu : us.len = W64 0
          · simp only [hu, _root_.decide_true, Bool.not_true]
            wp_auto
            wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            (try wp_auto)
            iapply HΦ
            unfold isWFDecisionLe
            iexists .noOpinion
            isplitr
            · iexact Hd
            · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
          · simp only [hu, _root_.decide_false, Bool.not_false]
            wp_auto
            wp_apply (wp_ConditionsAwareDecisionConditionsMap slice.nil slice.nil us (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) [] [] ul) $$ [$Hus] as %d ⟨#Hd, -⟩
            · iframe #
              isplitl []
              · iapply ownSlice_nil
              isplitl []
              · iapply ownSlice_nil
              repeat (first | iexact Hul | iexact Hal | (iapply BigSepL.bigSepL_nil.2; itrivial) | (iapply conds_app_intro_b2; isplitl []))
            (try wp_auto)
            iapply HΦ
            iexact Hd
        · simp only [he, _root_.decide_false, Bool.not_false]
          wp_auto
          wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
          ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
          · isplitr
            · iexact Hel
            · iexact Hagg
          (try wp_auto)
          wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
          · first | iassumption | iapply utilerrors.errTreeOrNil_nil
          (try wp_auto)
          iapply HΦ
          unfold isWFDecisionLe
          iexists .noOpinion
          isplitr
          · iexact Hd
          · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
      · simp only [hr, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_apply (wp_ConditionsAwareDecisionAllow) $$ [] as %d #Hd
        · first | iassumption | iapply utilerrors.errTreeOrNil_nil
        (try wp_auto)
        iapply HΦ
        unfold isWFDecisionLe
        iexists .allow
        isplitr
        · iexact Hd
        · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    simp only [h10, _root_.decide_false, Bool.not_false]
    wp_auto
    wp_apply (ConditionsMap.wp_ptr_NoOpinionConditions_of_b2 wp_ConditionsMap_NoOpinionConditions c_ptr
      (DFrac.own 1) c no) $$ [$c] as %it ⟨c, #Hit⟩
    · iexact Hsn
    (try wp_auto)
    wp_apply (wp_conditionsToAppliedErroredUnevaluated it no ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
    · iframe #
    (try wp_auto)
    wp_apply wp_string_len r as -
    by_cases hr : W64 r.length = W64 0
    · simp only [hr, _root_.decide_true, Bool.not_true]
      wp_auto
      by_cases he : es.len = W64 0
      · simp only [he, _root_.decide_true, Bool.not_true]
        wp_auto
        by_cases hu : us.len = W64 0
        · simp only [hu, _root_.decide_true, Bool.not_true]
          wp_auto
          by_cases h20 : c.allowConditions'.len = W64 0
          · simp only [h20, _root_.decide_true, Bool.not_true]
            wp_auto
            wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            (try wp_auto)
            iapply HΦ
            unfold isWFDecisionLe
            iexists .noOpinion
            isplitr
            · iexact Hd
            · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
          simp only [h20, _root_.decide_false, Bool.not_false]
          wp_auto
          wp_apply (ConditionsMap.wp_ptr_AllowConditions_of_b2 wp_ConditionsMap_AllowConditions c_ptr
            (DFrac.own 1) c al) $$ [$c] as %it ⟨c, #Hit⟩
          · iexact Hsa
          (try wp_auto)
          wp_apply (wp_conditionsToAppliedErroredUnevaluated it al ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
          · iframe #
          (try wp_auto)
          wp_apply wp_string_len r as -
          by_cases hr : W64 r.length = W64 0
          · simp only [hr, _root_.decide_true, Bool.not_true]
            wp_auto
            by_cases he : es.len = W64 0
            · simp only [he, _root_.decide_true, Bool.not_true]
              wp_auto
              by_cases hu : us.len = W64 0
              · simp only [hu, _root_.decide_true, Bool.not_true]
                wp_auto
                wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
                · first | iassumption | iapply utilerrors.errTreeOrNil_nil
                (try wp_auto)
                iapply HΦ
                unfold isWFDecisionLe
                iexists .noOpinion
                isplitr
                · iexact Hd
                · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
              · simp only [hu, _root_.decide_false, Bool.not_false]
                wp_auto
                wp_apply (wp_ConditionsAwareDecisionConditionsMap slice.nil slice.nil us (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) [] [] ul) $$ [$Hus] as %d ⟨#Hd, -⟩
                · iframe #
                  isplitl []
                  · iapply ownSlice_nil
                  isplitl []
                  · iapply ownSlice_nil
                  repeat (first | iexact Hul | iexact Hal | (iapply BigSepL.bigSepL_nil.2; itrivial) | (iapply conds_app_intro_b2; isplitl []))
                (try wp_auto)
                iapply HΦ
                iexact Hd
            · simp only [he, _root_.decide_false, Bool.not_false]
              wp_auto
              wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
              ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
              · isplitr
                · iexact Hel
                · iexact Hagg
              (try wp_auto)
              wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
              · first | iassumption | iapply utilerrors.errTreeOrNil_nil
              (try wp_auto)
              iapply HΦ
              unfold isWFDecisionLe
              iexists .noOpinion
              isplitr
              · iexact Hd
              · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
          · simp only [hr, _root_.decide_false, Bool.not_false]
            wp_auto
            wp_apply (wp_ConditionsAwareDecisionAllow) $$ [] as %d #Hd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            (try wp_auto)
            iapply HΦ
            unfold isWFDecisionLe
            iexists .allow
            isplitr
            · iexact Hd
            · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
        · simp only [hu, _root_.decide_false, Bool.not_false]
          wp_auto
          wp_apply (wp_ConditionsAwareDecisionConditionsMap slice.nil us c.allowConditions' (DFrac.own 1) (DFrac.own 1) DFrac.discard [] ul al) $$ [$Hus] as %d ⟨#Hd, -⟩
          · iframe #
            isplitl []
            · iapply ownSlice_nil
            repeat (first | iexact Hul | iexact Hal | (iapply BigSepL.bigSepL_nil.2; itrivial) | (iapply conds_app_intro_b2; isplitl []))
          (try wp_auto)
          iapply HΦ
          iexact Hd
      · simp only [he, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
        ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
        · isplitr
          · iexact Hel
          · iexact Hagg
        (try wp_auto)
        wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
        · first | iassumption | iapply utilerrors.errTreeOrNil_nil
        (try wp_auto)
        iapply HΦ
        unfold isWFDecisionLe
        iexists .noOpinion
        isplitr
        · iexact Hd
        · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    · simp only [hr, _root_.decide_false, Bool.not_false]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      (try wp_auto)
      iapply HΦ
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  simp only [h00, _root_.decide_false, Bool.not_false]
  wp_auto
  wp_apply (ConditionsMap.wp_ptr_DenyConditions_of_b2 wp_ConditionsMap_DenyConditions c_ptr
    (DFrac.own 1) c dn) $$ [$c] as %it ⟨c, #Hit⟩
  · iexact Hsd
  (try wp_auto)
  wp_apply (wp_conditionsToAppliedErroredUnevaluated it dn ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_string_len r as -
  by_cases hr : W64 r.length = W64 0
  · simp only [hr, _root_.decide_true, Bool.not_true]
    wp_auto
    by_cases he : es.len = W64 0
    · simp only [he, _root_.decide_true, Bool.not_true]
      wp_auto
      by_cases hu : us.len = W64 0
      · simp only [hu, _root_.decide_true, Bool.not_true]
        wp_auto
        by_cases h10 : c.noOpinionConditions'.len = W64 0
        · simp only [h10, _root_.decide_true, Bool.not_true]
          wp_auto
          by_cases h20 : c.allowConditions'.len = W64 0
          · simp only [h20, _root_.decide_true, Bool.not_true]
            wp_auto
            wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            (try wp_auto)
            iapply HΦ
            unfold isWFDecisionLe
            iexists .noOpinion
            isplitr
            · iexact Hd
            · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
          simp only [h20, _root_.decide_false, Bool.not_false]
          wp_auto
          wp_apply (ConditionsMap.wp_ptr_AllowConditions_of_b2 wp_ConditionsMap_AllowConditions c_ptr
            (DFrac.own 1) c al) $$ [$c] as %it ⟨c, #Hit⟩
          · iexact Hsa
          (try wp_auto)
          wp_apply (wp_conditionsToAppliedErroredUnevaluated it al ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
          · iframe #
          (try wp_auto)
          wp_apply wp_string_len r as -
          by_cases hr : W64 r.length = W64 0
          · simp only [hr, _root_.decide_true, Bool.not_true]
            wp_auto
            by_cases he : es.len = W64 0
            · simp only [he, _root_.decide_true, Bool.not_true]
              wp_auto
              by_cases hu : us.len = W64 0
              · simp only [hu, _root_.decide_true, Bool.not_true]
                wp_auto
                wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
                · first | iassumption | iapply utilerrors.errTreeOrNil_nil
                (try wp_auto)
                iapply HΦ
                unfold isWFDecisionLe
                iexists .noOpinion
                isplitr
                · iexact Hd
                · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
              · simp only [hu, _root_.decide_false, Bool.not_false]
                wp_auto
                wp_apply (wp_ConditionsAwareDecisionConditionsMap slice.nil slice.nil us (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) [] [] ul) $$ [$Hus] as %d ⟨#Hd, -⟩
                · iframe #
                  isplitl []
                  · iapply ownSlice_nil
                  isplitl []
                  · iapply ownSlice_nil
                  repeat (first | iexact Hul | iexact Hal | (iapply BigSepL.bigSepL_nil.2; itrivial) | (iapply conds_app_intro_b2; isplitl []))
                (try wp_auto)
                iapply HΦ
                iexact Hd
            · simp only [he, _root_.decide_false, Bool.not_false]
              wp_auto
              wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
              ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
              · isplitr
                · iexact Hel
                · iexact Hagg
              (try wp_auto)
              wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
              · first | iassumption | iapply utilerrors.errTreeOrNil_nil
              (try wp_auto)
              iapply HΦ
              unfold isWFDecisionLe
              iexists .noOpinion
              isplitr
              · iexact Hd
              · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
          · simp only [hr, _root_.decide_false, Bool.not_false]
            wp_auto
            wp_apply (wp_ConditionsAwareDecisionAllow) $$ [] as %d #Hd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            (try wp_auto)
            iapply HΦ
            unfold isWFDecisionLe
            iexists .allow
            isplitr
            · iexact Hd
            · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
        simp only [h10, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_apply (ConditionsMap.wp_ptr_NoOpinionConditions_of_b2 wp_ConditionsMap_NoOpinionConditions c_ptr
          (DFrac.own 1) c no) $$ [$c] as %it ⟨c, #Hit⟩
        · iexact Hsn
        (try wp_auto)
        wp_apply (wp_conditionsToAppliedErroredUnevaluated it no ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
        · iframe #
        (try wp_auto)
        wp_apply wp_string_len r as -
        by_cases hr : W64 r.length = W64 0
        · simp only [hr, _root_.decide_true, Bool.not_true]
          wp_auto
          by_cases he : es.len = W64 0
          · simp only [he, _root_.decide_true, Bool.not_true]
            wp_auto
            by_cases hu : us.len = W64 0
            · simp only [hu, _root_.decide_true, Bool.not_true]
              wp_auto
              by_cases h20 : c.allowConditions'.len = W64 0
              · simp only [h20, _root_.decide_true, Bool.not_true]
                wp_auto
                wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
                · first | iassumption | iapply utilerrors.errTreeOrNil_nil
                (try wp_auto)
                iapply HΦ
                unfold isWFDecisionLe
                iexists .noOpinion
                isplitr
                · iexact Hd
                · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
              simp only [h20, _root_.decide_false, Bool.not_false]
              wp_auto
              wp_apply (ConditionsMap.wp_ptr_AllowConditions_of_b2 wp_ConditionsMap_AllowConditions c_ptr
                (DFrac.own 1) c al) $$ [$c] as %it ⟨c, #Hit⟩
              · iexact Hsa
              (try wp_auto)
              wp_apply (wp_conditionsToAppliedErroredUnevaluated it al ev) as %r %es %us ⟨⟨%el, Hes, #Hel⟩, ⟨%ul, Hus, #Hul⟩⟩
              · iframe #
              (try wp_auto)
              wp_apply wp_string_len r as -
              by_cases hr : W64 r.length = W64 0
              · simp only [hr, _root_.decide_true, Bool.not_true]
                wp_auto
                by_cases he : es.len = W64 0
                · simp only [he, _root_.decide_true, Bool.not_true]
                  wp_auto
                  by_cases hu : us.len = W64 0
                  · simp only [hu, _root_.decide_true, Bool.not_true]
                    wp_auto
                    wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
                    · first | iassumption | iapply utilerrors.errTreeOrNil_nil
                    (try wp_auto)
                    iapply HΦ
                    unfold isWFDecisionLe
                    iexists .noOpinion
                    isplitr
                    · iexact Hd
                    · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
                  · simp only [hu, _root_.decide_false, Bool.not_false]
                    wp_auto
                    wp_apply (wp_ConditionsAwareDecisionConditionsMap slice.nil slice.nil us (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) [] [] ul) $$ [$Hus] as %d ⟨#Hd, -⟩
                    · iframe #
                      isplitl []
                      · iapply ownSlice_nil
                      isplitl []
                      · iapply ownSlice_nil
                      repeat (first | iexact Hul | iexact Hal | (iapply BigSepL.bigSepL_nil.2; itrivial) | (iapply conds_app_intro_b2; isplitl []))
                    (try wp_auto)
                    iapply HΦ
                    iexact Hd
                · simp only [he, _root_.decide_false, Bool.not_false]
                  wp_auto
                  wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
                  ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
                  · isplitr
                    · iexact Hel
                    · iexact Hagg
                  (try wp_auto)
                  wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
                  · first | iassumption | iapply utilerrors.errTreeOrNil_nil
                  (try wp_auto)
                  iapply HΦ
                  unfold isWFDecisionLe
                  iexists .noOpinion
                  isplitr
                  · iexact Hd
                  · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
              · simp only [hr, _root_.decide_false, Bool.not_false]
                wp_auto
                wp_apply (wp_ConditionsAwareDecisionAllow) $$ [] as %d #Hd
                · first | iassumption | iapply utilerrors.errTreeOrNil_nil
                (try wp_auto)
                iapply HΦ
                unfold isWFDecisionLe
                iexists .allow
                isplitr
                · iexact Hd
                · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
            · simp only [hu, _root_.decide_false, Bool.not_false]
              wp_auto
              wp_apply (wp_ConditionsAwareDecisionConditionsMap slice.nil us c.allowConditions' (DFrac.own 1) (DFrac.own 1) DFrac.discard [] ul al) $$ [$Hus] as %d ⟨#Hd, -⟩
              · iframe #
                isplitl []
                · iapply ownSlice_nil
                repeat (first | iexact Hul | iexact Hal | (iapply BigSepL.bigSepL_nil.2; itrivial) | (iapply conds_app_intro_b2; isplitl []))
              (try wp_auto)
              iapply HΦ
              iexact Hd
          · simp only [he, _root_.decide_false, Bool.not_false]
            wp_auto
            wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
            ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
            · isplitr
              · iexact Hel
              · iexact Hagg
            (try wp_auto)
            wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            (try wp_auto)
            iapply HΦ
            unfold isWFDecisionLe
            iexists .noOpinion
            isplitr
            · iexact Hd
            · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
        · simp only [hr, _root_.decide_false, Bool.not_false]
          wp_auto
          wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
          · first | iassumption | iapply utilerrors.errTreeOrNil_nil
          (try wp_auto)
          iapply HΦ
          unfold isWFDecisionLe
          iexists .noOpinion
          isplitr
          · iexact Hd
          · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
      · simp only [hu, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_apply (wp_ConditionsAwareDecisionConditionsMap us c.noOpinionConditions' c.allowConditions' (DFrac.own 1) DFrac.discard DFrac.discard ul no al) $$ [$Hus] as %d ⟨#Hd, -⟩
        · iframe #
          repeat (first | iexact Hul | iexact Hno | iexact Hal | (iapply conds_app_intro_b2; isplitl []))
        (try wp_auto)
        iapply HΦ
        iexact Hd
    · simp only [he, _root_.decide_false, Bool.not_false]
      wp_auto
      wp_apply (wp_NewAggregate es (DFrac.own 1) el) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
      ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' el agg $$ [Hagg]
      · isplitr
        · iexact Hel
        · iexact Hagg
      (try wp_auto)
      wp_apply (wp_ConditionsAwareDecisionDeny) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      (try wp_auto)
      iapply HΦ
      unfold isWFDecisionLe
      iexists .deny
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  · simp only [hr, _root_.decide_false, Bool.not_false]
    wp_auto
    wp_apply (wp_ConditionsAwareDecisionDeny) $$ [] as %d #Hd
    · first | iassumption | iapply utilerrors.errTreeOrNil_nil
    (try wp_auto)
    iapply HΦ
    unfold isWFDecisionLe
    iexists .deny
    isplitr
    · iexact Hd
    · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩

end proof

end authorizer
end EtcdGrove
end Perennial
