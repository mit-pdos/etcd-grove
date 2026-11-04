/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/NewDaemonSetsController.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: see the spec's header; the queues built with the item predicate `keyCanon`
(decision R5); `dscPools` from the expectations' and the consistency store's reader slots
(`threadPool.init`) and from the stores' pools (`infReaders`); the owner tokens' ghost map
allocated empty (`tokExcl` from `ownerTok_excl`), the consistency store's getters meeting
`getterContract`.

Still to add as hypotheses (callees without a spec yet): the four handler closures' contracts (`handlerSpec`, over this package's handler specs: `addDaemonset`, ...; see the header's open point 1), the pod write callback (`onWriteFnOk`, over `consistencyStore.WroteAt`), the getters' (`getterOk`, over `cache.LastStoreSyncResourceVersion`), `featureGate.Enabled` (through `dsGateIs`).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.NewDaemonSetsController
public import Spec.k8s_io.client_go.tools.record.NewBroadcaster
public import Spec.k8s_io.client_go.tools.record.WithContext
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.k8s_io.client_go.util.consistency.NewConsistencyStore
public import Spec.k8s_io.kubernetes.pkg.controller.NewControllerExpectations
public import Spec.k8s_io.client_go.util.workqueue.DefaultTypedControllerRateLimiter
public import Spec.k8s_io.client_go.util.workqueue.NewTypedRateLimitingQueueWithConfig
public import Spec.k8s_io.client_go.informers.apps.v1.daemonSetInformer__Informer
public import Spec.k8s_io.client_go.informers.apps.v1.daemonSetInformer__Lister
public import Spec.k8s_io.client_go.informers.apps.v1.controllerRevisionInformer__Informer
public import Spec.k8s_io.client_go.informers.apps.v1.controllerRevisionInformer__Lister
public import Spec.k8s_io.client_go.informers.core.v1.podInformer__Informer
public import Spec.k8s_io.client_go.informers.core.v1.podInformer__Lister
public import Spec.k8s_io.client_go.informers.core.v1.nodeInformer__Informer
public import Spec.k8s_io.client_go.informers.core.v1.nodeInformer__Lister
public import Spec.k8s_io.kubernetes.pkg.controller.AddPodNodeNameIndexer
public import Spec.k8s_io.kubernetes.pkg.controller.AddPodControllerIndexer
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.metrics.Register

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [klog_sem : k8s_io.klog.v2.Assumptions]
variable [cons_sem : k8s_io.client_go.util.consistency.Assumptions]
variable [ctl_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [wq_sem : k8s_io.client_go.util.workqueue.Assumptions]
variable [ainf_sem : k8s_io.client_go.informers.apps.v1.Assumptions]
variable [cinf_sem : k8s_io.client_go.informers.core.v1.Assumptions]

theorem NewDaemonSetsController.wp_proof
    (wp_NewBroadcaster : record.NewBroadcaster.spec (GF := GF) (hG := hG))
    (wp_WithContext : record.WithContext.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_NewConsistencyStore : consistency.NewConsistencyStore.spec (GF := GF) (hG := hG))
    (wp_NewControllerExpectations : NewControllerExpectations.spec (GF := GF) (hG := hG))
    (wp_DefRL : workqueue.DefaultTypedControllerRateLimiter.spec (GF := GF) (hG := hG))
    (wp_NewRLQ : workqueue.NewTypedRateLimitingQueueWithConfig.spec (GF := GF) (hG := hG))
    (wp_DSInformer : appsinformers.daemonSetInformer.Informer.spec (GF := GF) (hG := hG))
    (wp_DSLister : appsinformers.daemonSetInformer.Lister.spec (GF := GF) (hG := hG))
    (wp_CRInformer : appsinformers.controllerRevisionInformer.Informer.spec (GF := GF) (hG := hG))
    (wp_CRLister : appsinformers.controllerRevisionInformer.Lister.spec (GF := GF) (hG := hG))
    (wp_PodInformer : coreinformers.podInformer.Informer.spec (GF := GF) (hG := hG))
    (wp_PodLister : coreinformers.podInformer.Lister.spec (GF := GF) (hG := hG))
    (wp_NodeInformer : coreinformers.nodeInformer.Informer.spec (GF := GF) (hG := hG))
    (wp_NodeLister : coreinformers.nodeInformer.Lister.spec (GF := GF) (hG := hG))
    (wp_AddPodNodeNameIndexer : AddPodNodeNameIndexer.spec (GF := GF) (hG := hG))
    (wp_AddPodControllerIndexer : AddPodControllerIndexer.spec (GF := GF) (hG := hG))
    (wp_Register : dsmetrics.Register.spec (GF := GF) (hG := hG)) :
    NewDaemonSetsController.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
