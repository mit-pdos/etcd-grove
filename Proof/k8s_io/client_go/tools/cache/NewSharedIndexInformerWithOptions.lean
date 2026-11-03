/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewSharedIndexInformerWithOptions.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
The methods' specs build the `isInformer`/`infRunOk` contracts. Missing callee specs (next
round): `NewIndexer` (whose reader slots the proof puts in the informer's pool,
`infReaders`), `WithStoreMetrics`, `NewCacheMutationDetector`, `sync.NewCond`.
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewSharedIndexInformerWithOptions
public import Spec.fmt.Sprintf
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__AddEventHandlerWithOptions
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__AddIndexers
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__GetIndexer
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__GetStore
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__HasSynced
public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__RunWithContext

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

theorem NewSharedIndexInformerWithOptions.wp_proof
    (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_HasSynced : cache.sharedIndexInformer.HasSynced.spec (GF := GF) (hG := hG))
    (wp_GetStore : cache.sharedIndexInformer.GetStore.spec (GF := GF) (hG := hG))
    (wp_GetIndexer : cache.sharedIndexInformer.GetIndexer.spec (GF := GF) (hG := hG))
    (wp_AddIndexers : cache.sharedIndexInformer.AddIndexers.spec (GF := GF) (hG := hG))
    (wp_AddEventHandlerWithOptions : cache.sharedIndexInformer.AddEventHandlerWithOptions.spec (GF := GF) (hG := hG))
    (wp_RunWithContext : cache.sharedIndexInformer.RunWithContext.spec (GF := GF) (hG := hG)) :
    NewSharedIndexInformerWithOptions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
