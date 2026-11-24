/-
The proof of `arbAuthorizer.ConditionsAwareAuthorize.spec` (`Spec/github_com/mit_pdos/etcd_grove/e
xamples/k8s/authz/arbAuthorizer__ConditionsAwareAuthorize.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__ConditionsAwareAuthorize
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbDecision

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

theorem arbAuthorizer.ConditionsAwareAuthorize.wp_proof
    (wp_arbDecision : EtcdGrove.k8s_authz.arbDecision.spec (GF := GF) (hG := hG)) :
    arbAuthorizer.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG) := by
  intro z ctx a hz hz2
  wp_start
  wp_auto
  wp_apply (wp_arbDecision z.depth' hz hz2) as %d #Hd
  (try wp_auto)
  iapply HΦ
  iapply isWFDecisionBnd_weaken
  isplitl []
  · iexact Hd
  ipureintro; exact ⟨hz, hz2⟩

end proof

end k8s_authz
end EtcdGrove
end Perennial
