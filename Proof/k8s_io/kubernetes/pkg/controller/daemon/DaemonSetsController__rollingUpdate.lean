/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__rollingUpdate.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

`IsPodAvailable`'s spec is still to write (a hypothesis named here, the file to come). The loop over the map (`range` over a Go map: any order) keeps `oldPod = nil` by `findUpdatedPodsOnNode`'s post and `podsView`'s logged pods (`podOf`: the hash label).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__rollingUpdate
public import Spec.fmt.Errorf
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodAvailable
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__getNodesToDaemonPods
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncNodes
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__updatedDesiredNodeCounts
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.daemonPodTolerations
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.findUpdatedPodsOnNode
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.nodeShouldRunDaemonPod

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

theorem DaemonSetsController.rollingUpdate.wp_proof
    (wp_getNodesToDaemonPods : DaemonSetsController.getNodesToDaemonPods.spec (GF := GF) (hG := hG))
    (wp_updatedDesiredNodeCounts : DaemonSetsController.updatedDesiredNodeCounts.spec (GF := GF) (hG := hG))
    (wp_findUpdatedPodsOnNode : findUpdatedPodsOnNode.spec (GF := GF) (hG := hG))
    (wp_nodeShouldRunDaemonPod : nodeShouldRunDaemonPod.spec (GF := GF) (hG := hG))
    (wp_daemonPodTolerations : daemonPodTolerations.spec (GF := GF) (hG := hG))
    (wp_syncNodes : DaemonSetsController.syncNodes.spec (GF := GF) (hG := hG))
    (wp_IsPodAvailable : IsPodAvailable.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.rollingUpdate.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
