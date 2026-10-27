/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__reset.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__reset

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.reset.wp_proof : storeIndex.reset.spec (GF := GF) (hG := hG) := by
  intro i ip
  wp_start as Hind
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string index.ty) as %ip' Hip'
  (try wp_auto)
  iapply HΦ
  iexists ip'
  iframe
  iunfold ownIx
  rw [GMap.fmap_empty]
  iframe
  iapply BigSepM.bigSepM_empty.2; itrivial

end proof

end cache
end EtcdGrove
end Perennial
