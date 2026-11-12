/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__CreationObserved.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__CreationObserved
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__LowerExpectations

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]

theorem ControllerExpectations.CreationObserved.wp_proof
    (wp_Lower : ControllerExpectations.LowerExpectations.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.CreationObserved.spec (GF := GF) (hG := hG) := by
  intro r γe logger key
  wp_start as ⟨#Hexp, Hr⟩
  wp_auto
  wp_apply wp_Lower $$ [$Hexp $Hr] as Hr
  iapply HΦ; iframe

end proof

end dsctl
end EtcdGrove
end Perennial
