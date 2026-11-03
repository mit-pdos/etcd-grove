/-
Proof of `Spec/k8s_io/client_go/informers/core/v1/podInformer__defaultInformer.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
`MetaNamespaceIndexFunc` is not called by the body: its spec gives the namespace index's
contract (`fnOk … nsIdxFn`) that `NewTypedPodInformerWithOptions` takes.
-/
module

public import Spec.k8s_io.client_go.informers.core.v1.podInformer__defaultInformer
public import Spec.k8s_io.client_go.informers.core.v1.NewTypedPodInformerWithOptions
public import Spec.k8s_io.client_go.informers.sharedInformerFactory__InformerName
public import Spec.k8s_io.client_go.tools.cache.MetaNamespaceIndexFunc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace coreinformers

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem podInformer.defaultInformer.wp_proof
    (wp_InformerName : informers.sharedInformerFactory.InformerName.spec (GF := GF) (hG := hG))
    (wp_NewTypedPodInformerWithOptions : coreinformers.NewTypedPodInformerWithOptions.spec (GF := GF) (hG := hG))
    (wp_MetaNamespaceIndexFunc : cache.MetaNamespaceIndexFunc.spec (GF := GF) (hG := hG)) :
    podInformer.defaultInformer.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end coreinformers
end EtcdGrove
end Perennial
