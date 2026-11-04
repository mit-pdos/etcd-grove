/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__processNextWorkItem.lean`
over its callees' specs. Lean-first; Stage 3 of the autoverify run: a stub.

The proof's plan: `Get` gives `keyTok` of a canonical key (the queue's item predicate `keyCanon`); open `s1Inv`: the
owner `ownerOf key` registered (else register it: a fresh `ownerTok`, bound `0` with
`infRvLb 0` from the pod informer's invariant), its entry holds `syncTok` (not `keyTok`: ours is
exclusive); take it, leave `keyTok`; call the sync handler (`isDsc`'s `syncHandler`:
`syncDaemonSet`); open `s1Inv` again, swap back; `Done`.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__processNextWorkItem
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncDaemonSet
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Get
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Done
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Forget
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__AddRateLimited
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleError
public import Spec.fmt.Errorf

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [wq_sem : k8s_io.client_go.util.workqueue.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]

theorem DaemonSetsController.processNextWorkItem.wp_proof
    (wp_Get : workqueue.rateLimitingType.Get.spec (GF := GF) (hG := hG))
    (wp_Done : workqueue.rateLimitingType.Done.spec (GF := GF) (hG := hG))
    (wp_Forget : workqueue.rateLimitingType.Forget.spec (GF := GF) (hG := hG))
    (wp_AddRateLimited : workqueue.rateLimitingType.AddRateLimited.spec (GF := GF) (hG := hG))
    (wp_syncDaemonSet : DaemonSetsController.syncDaemonSet.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_HandleError : utilruntime.HandleError.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.processNextWorkItem.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
