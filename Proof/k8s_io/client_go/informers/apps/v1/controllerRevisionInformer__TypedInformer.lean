/-
Proof of `Spec/k8s_io/client_go/informers/apps/v1/controllerRevisionInformer__TypedInformer.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
-/
module

public import Spec.k8s_io.client_go.informers.apps.v1.controllerRevisionInformer__TypedInformer
public import Spec.k8s_io.client_go.informers.apps.v1.controllerRevisionInformer__defaultInformer
public import Spec.k8s_io.client_go.informers.sharedInformerFactory__InformerFor
public import Spec.k8s_io.client_go.tools.cache.NewTypedSharedIndexInformer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appsinformers

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.apps.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem controllerRevisionInformer.TypedInformer.wp_proof
    (wp_InformerFor : informers.sharedInformerFactory.InformerFor.spec (GF := GF) (hG := hG))
    (wp_defaultInformer : appsinformers.controllerRevisionInformer.defaultInformer.spec (GF := GF) (hG := hG))
    (wp_NewTypedSharedIndexInformer : cache.NewTypedSharedIndexInformer.spec (GF := GF) (hG := hG)) :
    controllerRevisionInformer.TypedInformer.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end appsinformers
end EtcdGrove
end Perennial
