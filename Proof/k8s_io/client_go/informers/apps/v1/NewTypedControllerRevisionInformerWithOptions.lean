/-
Proof of `Spec/k8s_io/client_go/informers/apps/v1/NewTypedControllerRevisionInformerWithOptions.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Gap D2: the function is names only, so the proof also needs its body as a named
hypothesis (`NewTypedControllerRevisionInformerWithOptions_body.lean`, from the scratch translator, as
`RealPodControl__createPods_body.lean`): not written yet. The `*ListWatch`'s `lwOk` from its
closures also needs `ListWatch.ListWithContext`/`WatchWithContext` specs (not written yet).
-/
module

public import Spec.k8s_io.client_go.informers.apps.v1.NewTypedControllerRevisionInformerWithOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__AppsV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.appsV1__ControllerRevisions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.revisionClient__List
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.revisionClient__Watch
public import Spec.k8s_io.client_go.tools.cache.InformerName__WithResource
public import Spec.k8s_io.client_go.tools.cache.NewSharedIndexInformerWithOptions
public import Spec.k8s_io.client_go.tools.cache.NewTypedSharedIndexInformer
public import Spec.k8s_io.client_go.tools.cache.ToListWatcherWithWatchListSemantics

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

theorem NewTypedControllerRevisionInformerWithOptions.wp_proof
    (wp_WithResource : cache.InformerName.WithResource.spec (GF := GF) (hG := hG))
    (wp_ToListWatcherWithWatchListSemantics : cache.ToListWatcherWithWatchListSemantics.spec (GF := GF) (hG := hG))
    (wp_NewSharedIndexInformerWithOptions : cache.NewSharedIndexInformerWithOptions.spec (GF := GF) (hG := hG))
    (wp_NewTypedSharedIndexInformer : cache.NewTypedSharedIndexInformer.spec (GF := GF) (hG := hG))
    (wp_AppsV1 : apimodel.Clientset.AppsV1.spec (GF := GF) (hG := hG))
    (wp_ControllerRevisions : apimodel.appsV1.ControllerRevisions.spec (GF := GF) (hG := hG))
    (wp_List : apimodel.revisionClient.List.spec (GF := GF) (hG := hG))
    (wp_Watch : apimodel.revisionClient.Watch.spec (GF := GF) (hG := hG)) :
    NewTypedControllerRevisionInformerWithOptions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end appsinformers
end EtcdGrove
end Perennial
