/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__processNextNodeUpdate.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: the node queue's `Get` (its key token, unused: node names need no exclusivity), `syncNodeUpdate`, `Done`.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__processNextNodeUpdate
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Get
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Done
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Forget
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__AddRateLimited
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncNodeUpdate
public import Spec.fmt.Errorf
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleError

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
variable [wq_sem : k8s_io.client_go.util.workqueue.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]

theorem DaemonSetsController.processNextNodeUpdate.wp_proof
    (wp_Get : workqueue.rateLimitingType.Get.spec (GF := GF) (hG := hG))
    (wp_Done : workqueue.rateLimitingType.Done.spec (GF := GF) (hG := hG))
    (wp_Forget : workqueue.rateLimitingType.Forget.spec (GF := GF) (hG := hG))
    (wp_AddRateLimited : workqueue.rateLimitingType.AddRateLimited.spec (GF := GF) (hG := hG))
    (wp_syncNodeUpdate : DaemonSetsController.syncNodeUpdate.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_HandleError : utilruntime.HandleError.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.processNextNodeUpdate.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
