/-
Proof of `Spec/k8s_io/client_go/listers/core/v1/nodeLister__Get.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.core.v1.nodeLister__Get

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corelisters

open Iris Iris.BI Iris.ProofMode cache listers k8s_io.client_go.listers.core.v1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.core.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

theorem nodeLister.Get.wp_proof
    (wp_Get : listers.ResourceIndexer.Get.spec (GF := GF) (hG := hG)) :
    nodeLister.Get.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf res l name
  iintro %Φ ⟨#Hpkg, #Hca, Hr, #HT, #Hl⟩ HAU
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers $$ []
  · iPkgInit
  wp_method_call
  wp_call
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  iapply (wp_Get k8s_io.api.core.v1.Node.ty ca ts γ OK Fam kf res ([] : GoString) name) $$ [Hr] HAU
  iframe
  isplitr
  · iexact Hlpkg
  isplitr
  · iexact Hca
  iexact HT

end proof

end corelisters
end EtcdGrove
end Perennial
