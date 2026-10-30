/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__SetExpectations.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__SetExpectations
public import Spec.k8s_io.utils.clock.RealClock__Now
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.github_com.go_logr.logr.Logger__Info
public import Spec.k8s_io.client_go.tools.cache.cache__Add
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor_ControlleeExpectations

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [meta_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]

theorem ControllerExpectations.SetExpectations.wp_proof
    (wp_Now : clock.RealClock.Now.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Add : cache.Add.spec (GF := GF) (hG := hG))
    (wp_Acc : apimeta.Accessor_ControlleeExpectations.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.SetExpectations.spec (GF := GF) (hG := hG) := by
  intro r γe logger key add del
  wp_start as #Hexp
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache $$ []
  · iPkgInit
  ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» $$ []
  · iPkgInit
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr $$ []
  · iPkgInit
  ihave #Hexp' := Hexp
  iunfold isExp at Hexp'
  icases Hexp' with ⟨#Hst, #Hca, #Hkf, #Hinv⟩
  wp_auto
  wp_apply wp_Now as %t -
  iStructNamed «$r0»
  ipersist key
  ipersist timestamp
  imod inv_alloc ceN ⊤ (iprop(∃ a d : w64, structFieldRef ControlleeExpectations go!"add" «$r0_ptr» ↦ a ∗
      structFieldRef ControlleeExpectations go!"del" «$r0_ptr» ↦ d)) $$ [add del] with #Hcinv
  · inext; iexists _, _; iframe
  ihave #Hce : isCE «$r0_ptr» key $$ []
  · iunfold isCE; iframe #
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %_sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_V $$ [$logger] as %_l' logger
  wp_apply wp_Info $$ [$Hsl] as -
  wp_method_call
  wp_call
  wp_auto
  ihave #HkeyOk := ceD_keyOk γe.kf «$r0_ptr» key $$ Hkf
  ihave #Hacc := ceD_rvAcc wp_Acc «$r0_ptr» key
  wp_bind
  iapply (wp_Add γe.ca γe.ts γe.γ ceOK fam0 γe.kf (ceD «$r0_ptr» key) (fun _ => key) (fun _ => none)
    (interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #«$r0_ptr»))
    $$ [$Hcpkg $Hca $HkeyOk $Hacc]
  · iframe #
    isplitr
    · iunfold ceD; iframe #; imodintro; ipureintro; rfl
    · iunfold ceOK; imodintro; iexists «$r0_ptr», key; iframe #; ipureintro; rfl
  inext
  iapply (exp_lin γe (fun σ => σ.update key
    (interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #«$r0_ptr») none)
    (fun σ h => expNN_update σ _ _ _ h (by simp [interface.mkOk])))
  iframe Hinv
  iintro %σ' %_ -
  wp_auto
  iapply HΦ; itrivial

end proof

end dsctl
end EtcdGrove
end Perennial
