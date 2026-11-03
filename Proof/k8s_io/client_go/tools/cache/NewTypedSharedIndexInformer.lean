/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewTypedSharedIndexInformer.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewTypedSharedIndexInformer
public import Spec.k8s_io.client_go.tools.cache.typedSharedIndexInformer__AddEventHandlerWithOptions_body
public import Spec.k8s_io.client_go.tools.cache.typedSharedIndexInformer__AddIndexers_body
public import Spec.k8s_io.client_go.tools.cache.typedSharedIndexInformer__GetIndexer_body
public import Spec.k8s_io.client_go.tools.cache.typedSharedIndexInformer__GetStore_body
public import Spec.k8s_io.client_go.tools.cache.typedSharedIndexInformer__HasSynced_body
public import Spec.k8s_io.client_go.tools.cache.typedSharedIndexInformer__RunWithContext_body

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem NewTypedSharedIndexInformer.wp_proof
    (h_AddEventHandlerWithOptions : typedSharedIndexInformer.AddEventHandlerWithOptions_body.spec (GF := GF) (hG := hG))
    (h_HasSynced : typedSharedIndexInformer.HasSynced_body.spec (GF := GF) (hG := hG))
    (h_GetStore : typedSharedIndexInformer.GetStore_body.spec (GF := GF) (hG := hG))
    (h_GetIndexer : typedSharedIndexInformer.GetIndexer_body.spec (GF := GF) (hG := hG))
    (h_AddIndexers : typedSharedIndexInformer.AddIndexers_body.spec (GF := GF) (hG := hG))
    (h_RunWithContext : typedSharedIndexInformer.RunWithContext_body.spec (GF := GF) (hG := hG)) :
    NewTypedSharedIndexInformer.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
