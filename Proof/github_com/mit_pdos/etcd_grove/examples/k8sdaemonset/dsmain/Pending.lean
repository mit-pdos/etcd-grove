/-
**The pending callees of the driver's `Link.lean`, supplied** (Stage 3 of the DaemonSet run, track
C): every callee of another package that `etc/link-lean-first-dsonepod.txt` marks `?`, as the
result the closed theorem `dsonepod_safe` (`Adequacy.lean`) instantiates the Link's pending
hypotheses with. Hand-written; Lean-first.

* The model API server's functions: its Link's results (`apimodel/Link.lean`), the ones over its
  own pending specs (`daemonSetClient.Create`, over `prepareDaemonSet`) applied to those, which are
  `sorry` here (`apimodel_*_pending`: specified, not proved, `notes/k8s-daemonset-plan.md` phase 3).
* Every other callee (the informer factory's, track A; the controller's constructor and `Run`,
  `NewBackOff`, track C; `util.GetTargetNodeName`, track B's proved leaf, not linked yet): `sorry`,
  **one per function, named after it** (`*_pending`). Each goes once the function's package is
  linked: its line in the list file becomes `@` (its Link's result) or its callees.

Each entry is a spec believed true of the Go code (review 1 (API), H1: the constructor's takes the
model's ambiguous writes off, decision R8), so none lets a caller derive `False`; the closed
theorem's one false step is `Main.wp_proof`'s named `hamb`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI

section pending
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]

/-! ### The model API server's pending specs (its Link's `links_pending`) -/

theorem apimodel_daemonSetStatusEqual_pending :
    apimodel.daemonSetStatusEqual.spec (GF := GF) (hG := hG) := by sorry
theorem apimodel_prepareDaemonSet_pending :
    apimodel.prepareDaemonSet.spec (GF := GF) (hG := hG) := by sorry
theorem apimodel_preparePod_pending :
    apimodel.preparePod.spec (GF := GF) (hG := hG) := by sorry
theorem apimodel_updateDaemonSetStatus_pending :
    apimodel.updateDaemonSetStatus.spec (GF := GF) (hG := hG) := by sorry
theorem apimodel_watcher_run_pending :
    apimodel.watcher.run.spec (GF := GF) (hG := hG) := by sorry

/-! ### The informer factory (track A), the controller (tracks B, C), not linked yet -/

theorem informers_NewSharedInformerFactory_pending :
    informers.NewSharedInformerFactory.spec (GF := GF) (hG := hG) := by sorry
theorem informers_sharedInformerFactory_Apps_pending :
    informers.sharedInformerFactory.Apps.spec (GF := GF) (hG := hG) := by sorry
theorem informers_sharedInformerFactory_Core_pending :
    informers.sharedInformerFactory.Core.spec (GF := GF) (hG := hG) := by sorry
theorem informers_sharedInformerFactory_Start_pending :
    informers.sharedInformerFactory.Start.spec (GF := GF) (hG := hG) := by sorry
theorem apps_group_V1_pending : informersapps.group.V1.spec (GF := GF) (hG := hG) := by sorry
theorem core_group_V1_pending : informerscore.group.V1.spec (GF := GF) (hG := hG) := by sorry
theorem v1_version_DaemonSets_pending :
    appsinformers.version.DaemonSets.spec (GF := GF) (hG := hG) := by sorry
theorem v1_version_ControllerRevisions_pending :
    appsinformers.version.ControllerRevisions.spec (GF := GF) (hG := hG) := by sorry
theorem v1_version_Pods_pending : coreinformers.version.Pods.spec (GF := GF) (hG := hG) := by sorry
theorem v1_version_Nodes_pending : coreinformers.version.Nodes.spec (GF := GF) (hG := hG) := by sorry
theorem daemon_NewDaemonSetsController_pending :
    dsctl.NewDaemonSetsController.spec (GF := GF) (hG := hG) := by sorry
theorem daemon_DaemonSetsController_Run_pending :
    dsctl.DaemonSetsController.Run.spec (GF := GF) (hG := hG) := by sorry
theorem flowcontrol_NewBackOff_pending :
    dsctl.flowcontrol.NewBackOff.spec (GF := GF) (hG := hG) := by sorry
theorem util_GetTargetNodeName_pending : dsctl.GetTargetNodeName.spec (GF := GF) (hG := hG) := by
  sorry

/-- **`Main(checks)`'s result**, the Link's `wp_Main` at the pending callees above. -/
theorem wp_Main_closed : dsmain.Main.spec (GF := GF) (hG := hG) :=
  dsmain.wp_Main
    apimodel.Clientset.wp_AppsV1 apimodel.Clientset.wp_CoreV1 apimodel.wp_NewServer
    apimodel.Server.wp_AdminClientset apimodel.Server.wp_Clientset apimodel.appsV1.wp_DaemonSets
    apimodel.coreV1.wp_Nodes apimodel.coreV1.wp_Pods
    (apimodel.daemonSetClient.wp_Create apimodel_daemonSetStatusEqual_pending
      apimodel_prepareDaemonSet_pending apimodel_preparePod_pending
      apimodel_updateDaemonSetStatus_pending apimodel_watcher_run_pending)
    apimodel.nodeClient.wp_Create apimodel.podClient.wp_List
    apps_group_V1_pending core_group_V1_pending daemon_DaemonSetsController_Run_pending
    daemon_NewDaemonSetsController_pending flowcontrol_NewBackOff_pending
    informers_NewSharedInformerFactory_pending informers_sharedInformerFactory_Apps_pending
    informers_sharedInformerFactory_Core_pending informers_sharedInformerFactory_Start_pending
    util_GetTargetNodeName_pending v1_version_ControllerRevisions_pending
    v1_version_DaemonSets_pending v1_version_Nodes_pending v1_version_Pods_pending

end pending

end dsmain
end EtcdGrove
end Perennial
