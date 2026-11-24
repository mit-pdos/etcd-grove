/-
The proof of `unionAuthzHandler.evaluateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/union/unionAuthzHandler__evaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__evaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.fmt.ErrorfLeaf
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

theorem unionAuthzHandler.evaluateConditions.wp_proof
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_ErrorfLeaf : EtcdGrove.fmt.ErrorfLeaf.spec (GF := GF) (hG := hG)) :
    unionAuthzHandler.evaluateConditions.spec (GF := GF) (hG := hG) := by
  intro h ctx name d data
  wp_start as ⟨#Hu, #Hd⟩
  iunfold isUnionAuthz at Hu
  icases Hu with ⟨%nas, %m, #Hch, #Hchs, #Hm, #Hms, -⟩
  wp_auto
  wp_apply (wp_map_lookup2 go.string Authorizer.ty h.nameToAuthorizer' m name DFrac.discard) $$ [$Hm] as -
  cases hl : m !! name with
  | none =>
    simp only [Option.isSome_none, Option.getD_none]
    wp_auto
    iunfold isWFDecisionFit at Hd
    icases Hd with ⟨%md, #Hdm, -, -⟩
    wp_apply (ConditionsAwareDecision.wp_ptr_FailureDecision_of wp_ConditionsAwareDecision_FailureDecision)
      $$ [$unevaluatedSubDecision] as unevaluatedSubDecision
    · iexact Hdm
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hs, -⟩
    (try wp_auto)
    wp_apply wp_ErrorfLeaf $$ [$Hs] as %ferr ⟨Hs, -⟩
    · fmt_args_ok
    (try wp_auto)
    iapply HΦ
    itrivial
  | some a =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    ihave #Ha := (BigSepM.bigSepM_lookup (Φ := fun _ a => isAuthorizer (GF := GF) a) (x := a) hl) $$ Hms
    iunfold isAuthorizer at Ha
    icases Ha with ⟨%ai, %Ha, #Hcaa, #Hec⟩
    subst Ha
    simp only
    ispecialize Hec $$ %ctx %d %data
    iunfold ecOk at Hec
    wp_bind (App (App (App (Val _) _) _) _)
    iapply Hec
    · iexact Hd
    iintro !> %dec %r %e -
    wp_auto
    iapply HΦ
    itrivial

end proof

end union
end EtcdGrove
end Perennial
