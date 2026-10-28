/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/NewControllerExpectations.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.NewControllerExpectations
public import Spec.k8s_io.client_go.tools.cache.NewStore

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

theorem NewControllerExpectations.wp_proof
    (wp_NewStore : cache.NewStore.spec (GF := GF) (hG := hG)) :
    NewControllerExpectations.spec (GF := GF) (hG := hG) := by
  intro kf
  wp_start as ⟨#Hg, #Hkf⟩
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_NewStore ceOK fam0 kf slice.nil (DFrac.own 1)) $$ [] as %ca ⟨%ts, %γ, #Hca, Hst, Hrds⟩
  · iapply ownSlice_nil
  wp_alloc r as Hr
  iStructNamed Hr
  ipersist Store
  let γe : ExpNames := ⟨ca, ts, γ, kf⟩
  imod inv_alloc expN ⊤ (expInv γe) $$ [Hst] with #Hinv
  · inext; iexists _; iframe; ipureintro; exact expNN_empty
  wp_auto
  iapply HΦ
  iexists γe
  isplitr
  · iunfold isExp; iframe #
  iunfold expReader
  iexact Hrds

end proof

end dsctl
end EtcdGrove
end Perennial
