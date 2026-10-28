/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__RaiseExpectations.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__RaiseExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__GetExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.ControlleeExpectations__Add
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.github_com.go_logr.logr.Logger__Info

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

theorem ControllerExpectations.RaiseExpectations.wp_proof
    (wp_GetExpectations : ControllerExpectations.GetExpectations.spec (GF := GF) (hG := hG))
    (wp_Add : ControlleeExpectations.Add.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.RaiseExpectations.spec (GF := GF) (hG := hG) := by
  intro r γe logger key add del
  wp_start as ⟨#Hexp, Hr⟩
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetExpectations $$ [$Hexp $Hr] as %e %ok ⟨Hr, Hrec⟩
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iclear Hrec
    wp_auto
    iapply HΦ; iframe
  · simp only [↓reduceIte]
    icases Hrec with ⟨%k, #Hce⟩
    wp_auto
    wp_apply wp_Add $$ [$Hce]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %_sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_V $$ [$logger] as %_l' logger
    wp_apply wp_Info $$ [$Hsl] as -
    iapply HΦ; iframe

end proof

end dsctl
end EtcdGrove
end Perennial
