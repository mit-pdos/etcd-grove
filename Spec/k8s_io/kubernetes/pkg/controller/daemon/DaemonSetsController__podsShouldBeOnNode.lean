/-
`(*DaemonSetsController).podsShouldBeOnNode(logger, node, nodeToDaemonPods, ds, hash,
tolerations, requiredNodeAffinity)` (`daemon_controller.go:849`): the node's pod to create and pods
to delete. Lean-first; Stage 3, track B.

**What S1 needs**: a node is to be created on only if the map has no entry for it. The code also
asks to create when surge is allowed and every pod on the node is being deleted, failed or
succeeded; the map's pods are logged ones (`podsView`), which `sceneOk` makes live and `Pending`,
so that branch is not taken (the backoff, event and failed-pod branches neither). The pods to
delete are any names.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`dsc.podsShouldBeOnNode(...)`**: see the file header. -/
abbrev DaemonSetsController.podsShouldBeOnNode.spec : Prop :=
∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (logger : github_com.go_logr.logr.Logger) (node : Loc)
    (n : kd.core.Node) (m : GoMap) (Mp : GMap GoString (List kd.core.Pod)) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (hash : GoString) (tl : GoSlice) (dq : DFrac)
    (tols : List k8s_io.api.core.v1.Toleration)
    (rna : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.RequiredNodeAffinity) (L : Nat),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ □ nodeAt node DFrac.discard n ∗ podMapAt m Mp ∗
      podsView γa d.ObjectMeta'.UID' L Mp ∗ dsArg γa ds o d ∗ tl ↦*{dq} tols ∗ rnaOk rna }}
    (App (App (App (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"podsShouldBeOnNode")) (Val #logger)) (Val #node)) (Val #m)) (Val #ds)) (Val #hash)) (Val #tl)) (Val #rna))
  {{ (nn pd : GoSlice), RET (PairV #nn #pd); threadTok ∗ podMapAt m Mp ∗ tl ↦*{dq} tols ∗
      ∃ (ns ps : List GoString), nn ↦* ns ∗ pd ↦* ps ∗
        ⌜∀ x ∈ ns, x = n.ObjectMeta'.Name' ∧ Mp !! x = none⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
