/-
Proof of `Spec/k8s_io/client_go/tools/cache/InformerNameAndResource__GroupVersionResource_ptr.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.InformerNameAndResource__GroupVersionResource_ptr

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem InformerNameAndResource.GroupVersionResource_ptr.wp_proof :
    InformerNameAndResource.GroupVersionResource_ptr.spec (GF := GF) (hG := hG) := by
  intro l dq n
  wp_start as Hl
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  iapply HΦ; iframe

end proof

end cache
end EtcdGrove
end Perennial
