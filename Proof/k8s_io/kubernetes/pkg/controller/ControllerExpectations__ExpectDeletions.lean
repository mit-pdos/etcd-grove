/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__ExpectDeletions.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__ExpectDeletions
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__SetExpectations

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]

theorem ControllerExpectations.ExpectDeletions.wp_proof
    (wp_Set : ControllerExpectations.SetExpectations.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.ExpectDeletions.spec (GF := GF) (hG := hG) := by
  intro r γe logger key dels
  wp_start as #Hexp
  wp_auto
  wp_apply wp_Set $$ [$Hexp]
  iapply HΦ; itrivial

end proof

end dsctl
end EtcdGrove
end Perennial
