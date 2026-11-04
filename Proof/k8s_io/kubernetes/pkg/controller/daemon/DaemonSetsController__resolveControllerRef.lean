/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__resolveControllerRef.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: a DaemonSet store reader slot borrowed from `dscPools`; the lister's `Get` linearizes inside the informer invariant (`infAt`), whose store is a past log's table (`dsSeen`).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__resolveControllerRef
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetLister__DaemonSets
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetNamespaceLister__Get

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
variable [appsl_sem : k8s_io.client_go.listers.apps.v1.Assumptions]

theorem DaemonSetsController.resolveControllerRef.wp_proof
    (wp_DSNs : appslisters.daemonSetLister.DaemonSets.spec (GF := GF) (hG := hG))
    (wp_DSGet : appslisters.daemonSetNamespaceLister.Get.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.resolveControllerRef.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
