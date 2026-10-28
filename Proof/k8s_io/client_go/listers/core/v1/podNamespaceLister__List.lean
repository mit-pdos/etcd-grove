/-
Proof of `Spec/k8s_io/client_go/listers/core/v1/podNamespaceLister__List.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.core.v1.podNamespaceLister__List

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corelisters

open Iris Iris.BI Iris.ProofMode cache listers k8s_io.client_go.listers.core.v1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.core.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

theorem podNamespaceLister.List.wp_proof
    (wp_List : listers.ResourceIndexer.List.spec (GF := GF) (hG := hG)) :
    podNamespaceLister.List.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf res ns sel F
  iintro %Φ ⟨#Hpkg, #Hca, Hr, #HT, #Hsel, #Hq⟩ HAU
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers $$ []
  · iPkgInit
  wp_method_call
  wp_call
  (try wp_auto)
  iapply (wp_List k8s_io.api.core.v1.Pod.ty ca ts γ OK Fam kf res ns sel F) $$ [Hr] HAU
  iframe
  isplitr
  · iexact Hlpkg
  isplitr
  · iexact Hca
  isplitr
  · iexact HT
  isplitr
  · iexact Hsel
  iexact Hq

end proof

end corelisters
end EtcdGrove
end Perennial
