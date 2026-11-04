/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/dsmain/run.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

See the spec's header for the plan.

Still to add as hypotheses (callees without a spec yet): the cancel function's (`WithCancel`'s post), `go.panic` (excluded by the admin writes' success).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.setFeatureGates
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.NewServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__AdminClientset
public import Perennial.Spec.context.Background
public import Perennial.Spec.context.WithCancel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__CoreV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.coreV1__Nodes
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.nodeClient__Create
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.newNode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__Clientset
public import Spec.k8s_io.client_go.informers.NewSharedInformerFactory
public import Spec.k8s_io.client_go.informers.sharedInformerFactory__Apps
public import Spec.k8s_io.client_go.informers.apps.group__V1
public import Spec.k8s_io.client_go.informers.sharedInformerFactory__Core
public import Spec.k8s_io.client_go.informers.core.group__V1
public import Spec.k8s_io.client_go.informers.apps.v1.version__DaemonSets
public import Spec.k8s_io.client_go.informers.apps.v1.version__ControllerRevisions
public import Spec.k8s_io.client_go.informers.core.v1.version__Pods
public import Spec.k8s_io.client_go.informers.core.v1.version__Nodes
public import Spec.k8s_io.client_go.util.flowcontrol.NewBackOff
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.NewDaemonSetsController
public import Spec.k8s_io.client_go.informers.sharedInformerFactory__Start
public import Perennial.Spec.context.cancelCtx__Done
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__AppsV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.appsV1__DaemonSets
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.daemonSetClient__Create
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.newDaemonSet
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.check
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI Iris.ProofMode apimodel dsctl informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
variable [inf_sem : k8s_io.client_go.informers.Assumptions]
variable [infa_sem : k8s_io.client_go.informers.apps.Assumptions]
variable [infc_sem : k8s_io.client_go.informers.core.Assumptions]
variable [ainf_sem : k8s_io.client_go.informers.apps.v1.Assumptions]
variable [cinf_sem : k8s_io.client_go.informers.core.v1.Assumptions]
variable [fc_sem : k8s_io.client_go.util.flowcontrol.Assumptions]
variable [ds_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [time_sem : _root_.Perennial.time.Assumptions]

theorem run.wp_proof
    (wp_setFeatureGates : dsmain.setFeatureGates.spec (GF := GF) (hG := hG))
    (wp_NewServer : apimodel.NewServer.spec (GF := GF) (hG := hG))
    (wp_AdminClientset : apimodel.Server.AdminClientset.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (wp_WithCancel : context.WithCancel.spec (GF := GF) (hG := hG))
    (wp_CoreV1 : apimodel.Clientset.CoreV1.spec (GF := GF) (hG := hG))
    (wp_Nodes : apimodel.coreV1.Nodes.spec (GF := GF) (hG := hG))
    (wp_NodeCreate : apimodel.nodeClient.Create.spec (GF := GF) (hG := hG))
    (wp_newNode : dsmain.newNode.spec (GF := GF) (hG := hG))
    (wp_Clientset : apimodel.Server.Clientset.spec (GF := GF) (hG := hG))
    (wp_NewSharedInformerFactory : informers.NewSharedInformerFactory.spec (GF := GF) (hG := hG))
    (wp_FacApps : informers.sharedInformerFactory.Apps.spec (GF := GF) (hG := hG))
    (wp_AppsV1Group : informersapps.group.V1.spec (GF := GF) (hG := hG))
    (wp_FacCore : informers.sharedInformerFactory.Core.spec (GF := GF) (hG := hG))
    (wp_CoreV1Group : informerscore.group.V1.spec (GF := GF) (hG := hG))
    (wp_VDaemonSets : appsinformers.version.DaemonSets.spec (GF := GF) (hG := hG))
    (wp_VControllerRevisions : appsinformers.version.ControllerRevisions.spec (GF := GF) (hG := hG))
    (wp_VPods : coreinformers.version.Pods.spec (GF := GF) (hG := hG))
    (wp_VNodes : coreinformers.version.Nodes.spec (GF := GF) (hG := hG))
    (wp_NewBackOffD : dsctl.flowcontrol.NewBackOff.spec (GF := GF) (hG := hG))
    (wp_NewDaemonSetsController : dsctl.NewDaemonSetsController.spec (GF := GF) (hG := hG))
    (wp_FacStart : informers.sharedInformerFactory.Start.spec (GF := GF) (hG := hG))
    (wp_CtxDone : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_DscRun : dsctl.DaemonSetsController.Run.spec (GF := GF) (hG := hG))
    (wp_AppsV1 : apimodel.Clientset.AppsV1.spec (GF := GF) (hG := hG))
    (wp_DaemonSets : apimodel.appsV1.DaemonSets.spec (GF := GF) (hG := hG))
    (wp_DSCreate : apimodel.daemonSetClient.Create.spec (GF := GF) (hG := hG))
    (wp_newDaemonSet : dsmain.newDaemonSet.spec (GF := GF) (hG := hG))
    (wp_check : dsmain.check.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsmain
end EtcdGrove
end Perennial
