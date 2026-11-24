/-
The proof of `arbAuthorizer.EvaluateConditions.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbAuthorizer__EvaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__EvaluateConditions
public import Spec.math.rand.Int63n
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbDecisionValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbReason
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbMaybeEval
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.PartiallyEvaluateConditionsAwareDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnconditionalPartsOrFailClosed
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbEval
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__Evaluate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.B6Lemmas
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem arbAuthorizer.EvaluateConditions.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_arbDecisionValue : EtcdGrove.k8s_authz.arbDecisionValue.spec (GF := GF) (hG := hG))
    (wp_arbReason : EtcdGrove.k8s_authz.arbReason.spec (GF := GF) (hG := hG))
    (wp_arbErr : EtcdGrove.k8s_authz.arbErr.spec (GF := GF) (hG := hG))
    (wp_arbMaybeEval : EtcdGrove.k8s_authz.arbMaybeEval.spec (GF := GF) (hG := hG))
    (wp_PartiallyEvaluateConditionsAwareDecision : EtcdGrove.authorizer.PartiallyEvaluateConditionsAwareDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnconditionalPartsOrFailClosed : EtcdGrove.authorizer.ConditionsAwareDecision.UnconditionalPartsOrFailClosed.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (wp_arbEval : EtcdGrove.k8s_authz.arbEval.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_Evaluate : EtcdGrove.authorizer.ConditionsMap.Evaluate.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG)) :
    arbAuthorizer.EvaluateConditions.spec (GF := GF) (hG := hG) := by
  intro z ctx d data
  wp_start as #Hwf
  iunfold isWFDecisionFit at Hwf
  icases Hwf with ⟨%m, #Hd, %Hm', #Hdn⟩
  have Hm := Hm'.1
  wp_auto
  wp_apply wp_Int63n as %x %Hx
  · ipureintro; decide
  rcases int63n_4_cases x Hx with rfl | rfl | rfl | rfl
  · -- a lying authorizer
    wp_auto
    wp_apply wp_arbDecisionValue as %k _
    (try wp_auto)
    wp_apply wp_arbReason as %r _
    (try wp_auto)
    wp_apply wp_arbErr as %e _
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- partial evaluation
    wp_auto
    wp_apply (wp_PartiallyEvaluateConditionsAwareDecision ctx d m data _ authzNameMax) as %d' #Hwf'
    · iframe #
      isplitr
      · ipureintro; exact Hm
      isplitr
      · ipureintro; exact Hm'.2
      iunfold maybeEvalFnOk
      iright
      iintro %ctx' %cond %data'
      iunfold maybeEvalCallOk
      iintro !> %Ψ _ HΨ
      wp_apply wp_arbMaybeEval as %r #Hr
      iapply HΨ
      iexact Hr
    iunfold isWFDecisionBnd at Hwf'
    icases Hwf' with ⟨%m', #Hd', %Hm'', -⟩
    (try wp_auto)
    wp_apply (wp_ptr_UnconditionalPartsOrFailClosed_of
      wp_ConditionsAwareDecision_UnconditionalPartsOrFailClosed pd_ptr (DFrac.own 1) d' m')
      $$ [$pd] as %dec %r %e Hpd
    · iexact Hd'
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- full evaluation of a conditions map
    wp_auto
    wp_apply (wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap d_ptr
      (DFrac.own 1) d) $$ [$d] as Hdp
    icases isDecision_tag d m $$ Hd with %Htag
    rw [Htag, Dec.tag_cmap]
    cases hC : m.isCMap
    · wp_auto
      wp_apply (ConditionsAwareDecision.wp_ptr_FailureDecision_of
        wp_ConditionsAwareDecision_FailureDecision d_ptr (DFrac.own 1) d m) $$ [$Hdp] as Hdp
      · iexact Hd
      ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer $$ []
      · iPkgInit
      ihave #Hai : (authorizerInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hapkg
      iunfold authorizerInit at Hai
      icases Hai with ⟨%e0, #He0⟩
      (try wp_auto)
      iapply HΦ
      itrivial
    · cases m with
      | cmap dn no al =>
        wp_auto
        wp_apply (wp_ptr_ConditionsMap_of wp_ConditionsAwareDecision_ConditionsMap d_ptr
          (DFrac.own 1) d) $$ [$Hdp] as Hdp
        (try wp_auto)
        wp_apply (wp_ConditionsMap_Evaluate d.conditionsMap' dn no al ctx data _) as %dec %r %e _
        · isplitr
          · iapply isDecision_cmap
            iexact Hd
          iunfold evalFnOk
          iintro %ctx' %cond %data'
          iunfold evalCallOk
          iintro !> %Ψ _ HΨ
          wp_apply wp_arbEval as %b %e #He
          iapply HΨ
          iexact He
        (try wp_auto)
        iapply HΦ
        itrivial
      | _ => simp [Dec.isCMap] at hC
  · ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer $$ []
    · iPkgInit
    ihave #Hai : (authorizerInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hapkg
    iunfold authorizerInit at Hai
    icases Hai with ⟨%e0, #He0⟩
    wp_auto
    iapply HΦ
    itrivial

end proof

end k8s_authz
end EtcdGrove
end Perennial
