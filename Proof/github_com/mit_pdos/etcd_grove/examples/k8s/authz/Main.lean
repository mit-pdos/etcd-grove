/-
The proof of `Main.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/Main.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.Main
public import Perennial.Spec.context.Background
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.newChain
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__ConditionsAwareAuthorize
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.twoPhase

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

theorem Main.wp_proof
    (wp_Background : _root_.Perennial.context.Background.spec (GF := GF) (hG := hG))
    (wp_newChain : EtcdGrove.k8s_authz.newChain.spec (GF := GF) (hG := hG))
    (wp_unionAuthzHandler_ConditionsAwareAuthorize : EtcdGrove.union.unionAuthzHandler.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG))
    (wp_twoPhase : EtcdGrove.k8s_authz.twoPhase.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_Background
  (try wp_auto)
  wp_apply wp_newChain as %a %err Hres
  icases Hres with (%Hne | ⟨%Heq, %h, %Ha, #Hu⟩)
  · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      itrivial
  · subst Heq Ha
    wp_auto
    wp_apply wp_unionAuthzHandler_ConditionsAwareAuthorize as %d Hwfd
    · iexact Hu
    iunfold isWFDecisionBnd at Hwfd
    icases Hwfd with ⟨%m, #Hd, %Hwf, #Hdn⟩
    (try wp_auto)
    wp_apply (wp_twoPhase _ h d m)
    · iframe #
      ipureintro; exact Hwf
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s_authz
end EtcdGrove
end Perennial
