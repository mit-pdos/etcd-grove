/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__SatisfiedExpectations.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__SatisfiedExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__GetExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.ControlleeExpectations__Fulfilled
public import Spec.k8s_io.kubernetes.pkg.controller.ControlleeExpectations__isExpired
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]

theorem ControllerExpectations.SatisfiedExpectations.wp_proof
    (wp_GetExpectations : ControllerExpectations.GetExpectations.spec (GF := GF) (hG := hG))
    (wp_Fulfilled : ControlleeExpectations.Fulfilled.spec (GF := GF) (hG := hG))
    (wp_isExpired : ControlleeExpectations.isExpired.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.SatisfiedExpectations.spec (GF := GF) (hG := hG) := by
  intro r γe logger key
  wp_start as ⟨#Hexp, Hr⟩
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetExpectations $$ [$Hexp $Hr] as %e %ok ⟨Hr, Hrec⟩
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iclear Hrec
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %_sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_V $$ [$logger] as %_l' logger
    wp_apply wp_Info $$ [$Hsl] as -
    iapply HΦ; iframe
  · simp only [↓reduceIte]
    icases Hrec with ⟨%k, #Hce⟩
    wp_auto
    wp_apply wp_Fulfilled $$ [$Hce] as %b1 -
    cases b1
    · wp_auto
      wp_apply wp_isExpired $$ [$Hce] as %b2 -
      cases b2
      · wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %_sl ⟨Hsl, -⟩
        (try wp_auto)
        wp_apply wp_V $$ [$logger] as %_l' logger
        wp_apply wp_Info $$ [$Hsl] as -
        iapply HΦ; iframe
      · wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %_sl ⟨Hsl, -⟩
        (try wp_auto)
        wp_apply wp_V $$ [$logger] as %_l' logger
        wp_apply wp_Info $$ [$Hsl] as -
        iapply HΦ; iframe
    · wp_auto
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
