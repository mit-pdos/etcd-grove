/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__updateDaemonset.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: the event's facts (`evFacts`, the informer's) give the objects' types and their place in the API log; reader slots borrowed from `dscPools` with the token.

Still to add as hypotheses (callees without a spec yet): `controller.KeyFunc`.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__updateDaemonset
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__deleteDaemonset
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__enqueue
public import Spec.fmt.Errorf
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleError
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
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]
variable [klog_sem : k8s_io.klog.v2.Assumptions]

theorem DaemonSetsController.updateDaemonset.wp_proof
    (wp_deleteDaemonset : DaemonSetsController.deleteDaemonset.spec (GF := GF) (hG := hG))
    (wp_enqueue : DaemonSetsController.enqueue.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_HandleError : utilruntime.HandleError.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_KObj : klog.KObj.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.updateDaemonset.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
