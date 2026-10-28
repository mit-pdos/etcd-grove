/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControllerExpectations__GetExpectations.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__GetExpectations
public import Spec.k8s_io.client_go.tools.cache.cache__GetByKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem ControllerExpectations.GetExpectations.wp_proof
    (wp_GetByKey : cache.GetByKey.spec (GF := GF) (hG := hG)) :
    ControllerExpectations.GetExpectations.spec (GF := GF) (hG := hG) := by
  intro r γe key
  wp_start as ⟨#Hexp, Hr⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache $$ []
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
    iunfold ceOK at HOK
    icases HOK with ⟨%e, %k, %he, #Hce⟩
    rw [he]
    wp_auto
    iapply HΦ
    iunfold expReader
    iframe
    simp only [↓reduceIte]
    iexists k
    iframe #
  · rw [decide_eq_false hin]
    wp_auto
    iapply HΦ
    iunfold expReader
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial

end proof

end dsctl
end EtcdGrove
end Perennial
