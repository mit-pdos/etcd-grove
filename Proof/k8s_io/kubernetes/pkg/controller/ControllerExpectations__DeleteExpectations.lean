/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__DeleteExpectations.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__DeleteExpectations
public import Spec.k8s_io.client_go.tools.cache.cache__GetByKey
public import Spec.k8s_io.client_go.tools.cache.cache__Delete
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

theorem ControllerExpectations.DeleteExpectations.wp_proof
    (wp_GetByKey : cache.GetByKey.spec (GF := GF) (hG := hG))
    (wp_Delete : cache.Delete.spec (GF := GF) (hG := hG))
    (wp_Acc : apimeta.Accessor_ControlleeExpectations.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.DeleteExpectations.spec (GF := GF) (hG := hG) := by
  intro r γe logger key
  wp_start as ⟨#Hexp, Hr⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache $$ []
  · iPkgInit
  ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» $$ []
  · iPkgInit
  ihave #Hexp' := Hexp
  iunfold isExp at Hexp'
  icases Hexp' with ⟨#Hst, #Hca, #Hkf, #Hinv⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iunfold expReader at Hr
  wp_bind
  iapply (wp_GetByKey γe.ca γe.ts γe.γ ceOK fam0 γe.kf key) $$ [$Hcpkg $Hca $Hr]
  inext
  iapply (exp_lin γe (fun σ => σ) (fun _ h => h))
  iframe Hinv
  iintro %σ %Hnn %item %ok ⟨%Hitem, #Hok, Hr⟩
  obtain ⟨rfl, rfl⟩ := Hitem
  by_cases hin : key ∈ σ.items
  · rw [decide_eq_true hin]
    have hnn : objAt σ.items key ≠ interface.nil := by
      rw [GMap.mem_iff] at hin
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hin
      unfold objAt; rw [ho]; exact Hnn key o ho
    iunfold okNil at Hok
    icases Hok with (%h | #HOK)
    · exact absurd h hnn
    ihave #HOK' := HOK
    iunfold ceOK at HOK'
    icases HOK' with ⟨%e, %k, %he, #Hce⟩
    ihave #Hce' := Hce
    iunfold isCE at Hce'
    icases Hce' with ⟨#Hk, -, -⟩
    rw [he]
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    ihave #HkeyOk := ceD_keyOk γe.kf e k $$ Hkf
    ihave #Hacc := ceD_rvAcc wp_Acc e k
    wp_bind
    iapply (wp_Delete γe.ca γe.ts γe.γ ceOK fam0 γe.kf (ceD e k) (fun _ => k) (fun _ => none)
      (interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #e))
      $$ [$Hcpkg $Hca $HkeyOk $Hacc]
    · iframe #
      iunfold ceD
      iframe #
      imodintro; ipureintro; rfl
    inext
    iapply (exp_lin γe (fun σ => σ.delete k (rvOfObj (fun _ => none)
      (interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #e)))
      (fun σ h => expNN_delete σ _ _ h))
    iframe Hinv
    iintro %σ' %_ -
    wp_auto
    iapply HΦ
    iunfold expReader
    iframe
  · rw [decide_eq_false hin]
    wp_auto
    iapply HΦ
    iunfold expReader
    iframe

end proof

end dsctl
end EtcdGrove
end Perennial
