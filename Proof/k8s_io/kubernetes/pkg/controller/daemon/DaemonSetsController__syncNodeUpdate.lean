/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__syncNodeUpdate.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: reader slots borrowed from `dscPools` with the token; every DaemonSet listed is a logged one (`dsSeen`), so its key is canonical (`sceneOk` in `s1Inv`) for `enqueue`.

Still to add as hypotheses (callees without a spec yet): `apierrors.IsNotFound`, `metav1.GetControllerOf` (names only), the DaemonSet lister's `List` (the cluster-wide `ListAll`), `controller.KeyFunc` (`DeletionHandlingMetaNamespaceKeyFunc`).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncNodeUpdate
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.k8s_io.client_go.listers.core.v1.nodeLister__Get
public import Spec.k8s_io.apimachinery.pkg.labels.Everything
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetNamespaceLister__List
public import Spec.k8s_io.client_go.tools.cache.cache__ByIndex
public import Spec.k8s_io.client_go.tools.cache.ObjectName__String
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.NodeShouldRunDaemonPod
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__enqueue
public import Spec.fmt.Errorf
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.github_com.go_logr.logr.Logger__Info
public import Spec.k8s_io.klog.v2.KObj

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
variable [corel_sem : k8s_io.client_go.listers.core.v1.Assumptions]
variable [appsl_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]

theorem DaemonSetsController.syncNodeUpdate.wp_proof
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_NodeGet : corelisters.nodeLister.Get.spec (GF := GF) (hG := hG))
    (wp_Everything : labels.Everything.spec (GF := GF) (hG := hG))
    (wp_DSList : appslisters.daemonSetNamespaceLister.List.spec (GF := GF) (hG := hG))
    (wp_ByIndex : cache.cache.ByIndex.spec (GF := GF) (hG := hG))
    (wp_ObjectNameString : cache.ObjectName.String.spec (GF := GF) (hG := hG))
    (wp_NodeShouldRunDaemonPod : NodeShouldRunDaemonPod.spec (GF := GF) (hG := hG))
    (wp_enqueue : DaemonSetsController.enqueue.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_KObj : klog.KObj.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.syncNodeUpdate.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
