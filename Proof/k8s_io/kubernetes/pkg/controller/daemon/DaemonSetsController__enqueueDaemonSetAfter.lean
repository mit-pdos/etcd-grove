/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__enqueueDaemonSetAfter.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: as `enqueue`, with `AddAfter`.

Still to add as hypotheses (callees without a spec yet): `DeletionHandlingMetaNamespaceKeyFunc`.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__enqueueDaemonSetAfter
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__AddAfter
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

theorem DaemonSetsController.enqueueDaemonSetAfter.wp_proof
    (wp_AddAfter : workqueue.rateLimitingType.AddAfter.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_HandleError : utilruntime.HandleError.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.enqueueDaemonSetAfter.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
