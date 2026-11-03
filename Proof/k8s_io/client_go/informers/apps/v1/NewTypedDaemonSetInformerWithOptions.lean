/-
Proof of `Spec/k8s_io/client_go/informers/apps/v1/NewTypedDaemonSetInformerWithOptions.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Gap D2: the function is names only, so the proof also needs its body as a named
hypothesis (`NewTypedDaemonSetInformerWithOptions_body.lean`, from the scratch translator, as
`RealPodControl__createPods_body.lean`): not written yet. The `*ListWatch`'s `lwOk` from its
closures also needs `ListWatch.ListWithContext`/`WatchWithContext` specs (not written yet).
-/
module

public import Spec.k8s_io.client_go.informers.apps.v1.NewTypedDaemonSetInformerWithOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__AppsV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.appsV1__DaemonSets
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.daemonSetClient__List
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.daemonSetClient__Watch
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

theorem NewTypedDaemonSetInformerWithOptions.wp_proof
    (wp_WithResource : cache.InformerName.WithResource.spec (GF := GF) (hG := hG))
    (wp_ToListWatcherWithWatchListSemantics : cache.ToListWatcherWithWatchListSemantics.spec (GF := GF) (hG := hG))
    (wp_NewSharedIndexInformerWithOptions : cache.NewSharedIndexInformerWithOptions.spec (GF := GF) (hG := hG))
    (wp_NewTypedSharedIndexInformer : cache.NewTypedSharedIndexInformer.spec (GF := GF) (hG := hG))
    (wp_AppsV1 : apimodel.Clientset.AppsV1.spec (GF := GF) (hG := hG))
    (wp_DaemonSets : apimodel.appsV1.DaemonSets.spec (GF := GF) (hG := hG))
    (wp_List : apimodel.daemonSetClient.List.spec (GF := GF) (hG := hG))
    (wp_Watch : apimodel.daemonSetClient.Watch.spec (GF := GF) (hG := hG)) :
    NewTypedDaemonSetInformerWithOptions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end appsinformers
end EtcdGrove
end Perennial
