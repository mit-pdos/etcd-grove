/-
Proof of `Spec/k8s_io/client_go/listers/apps/v1/daemonSetNamespaceLister__Get.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetNamespaceLister__Get

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI Iris.ProofMode cache listers k8s_io.client_go.listers.apps.v1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

theorem daemonSetNamespaceLister.Get.wp_proof
    (wp_Get : listers.ResourceIndexer.Get.spec (GF := GF) (hG := hG)) :
    daemonSetNamespaceLister.Get.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf res ns name
  iintro %Φ ⟨#Hpkg, #Hca, Hr, #HT⟩ HAU
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers $$ []
  · iPkgInit
  wp_method_call
  wp_call
  (try wp_auto)
  iapply (wp_Get k8s_io.api.apps.v1.DaemonSet.ty ca ts γ OK Fam kf res ns name) $$ [Hr] HAU
  iframe
  isplitr
  · iexact Hlpkg
  isplitr
  · iexact Hca
  iexact HT

end proof

end appslisters
end EtcdGrove
end Perennial
