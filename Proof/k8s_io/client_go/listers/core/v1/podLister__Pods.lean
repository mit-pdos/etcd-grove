/-
Proof of `Spec/k8s_io/client_go/listers/core/v1/podLister__Pods.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.core.v1.podLister__Pods
public import Spec.k8s_io.client_go.listers.NewNamespaced

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corelisters

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.listers.core.v1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.core.v1.Assumptions]

theorem podLister.Pods.wp_proof
    (wp_NewNamespaced : listers.NewNamespaced.spec (GF := GF) (hG := hG)) :
    podLister.Pods.spec (GF := GF) (hG := hG) := by
  intro s dq ri ns
  wp_start as Hs
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNamespaced
  (try wp_auto)
  iapply HΦ
  iexact Hs

end proof

end corelisters
end EtcdGrove
end Perennial
