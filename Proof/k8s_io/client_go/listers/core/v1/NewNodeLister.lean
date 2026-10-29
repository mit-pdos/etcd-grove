/-
Proof of `Spec/k8s_io/client_go/listers/core/v1/NewNodeLister.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.core.v1.NewNodeLister
public import Spec.k8s_io.client_go.listers.New
public import Spec.k8s_io.api.core.v1.Resource

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corelisters

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.listers.core.v1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.core.v1.Assumptions]

theorem NewNodeLister.wp_proof (wp_Resource : corev1.Resource.spec (GF := GF) (hG := hG))
    (wp_New : listers.New.spec (GF := GF) (hG := hG)) :
    NewNodeLister.spec (GF := GF) (hG := hG) := by
  intro idx
  wp_start
  ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.core.v1 $$ []
  · iPkgInit
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Resource as %res -
  (try wp_auto)
  wp_apply wp_New
  (try wp_auto)
  wp_apply wp_alloc as %l Hl
  (try wp_auto)
  ihave Hacc := (nodeLister.nodeLister_access_load_ResourceIndexer l _ (DFrac.own 1)).access_strict $$ Hl
  icases Hacc with ⟨Hf, -⟩
  iapply HΦ
  iexact Hf

end proof

end corelisters
end EtcdGrove
end Perennial
