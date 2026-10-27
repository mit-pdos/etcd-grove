/-
Proof of `Spec/k8s_io/client_go/listers/apps/v1/NewControllerRevisionLister.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.apps.v1.NewControllerRevisionLister
public import Spec.k8s_io.client_go.listers.New
public import Spec.k8s_io.api.apps.v1.Resource

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.listers.apps.v1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]

theorem NewControllerRevisionLister.wp_proof (wp_Resource : appsv1.Resource.spec (GF := GF) (hG := hG))
    (wp_New : listers.New.spec (GF := GF) (hG := hG)) :
    NewControllerRevisionLister.spec (GF := GF) (hG := hG) := by
  intro idx
  wp_start
  ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.apps.v1 $$ []
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
  ihave Hacc := (controllerRevisionLister.controllerRevisionLister_access_load_ResourceIndexer l _ (DFrac.own 1)).access_strict $$ Hl
  icases Hacc with ⟨Hf, -⟩
  iapply HΦ
  iexact Hf

end proof

end appslisters
end EtcdGrove
end Perennial
