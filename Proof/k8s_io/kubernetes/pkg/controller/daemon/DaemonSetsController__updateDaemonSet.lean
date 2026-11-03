/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__updateDaemonSet.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

A glue proof (Stage 3, step 3).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__updateDaemonSet
public import Spec.fmt.Errorf
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__SatisfiedExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__cleanupHistory
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__manage
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__rollingUpdate

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

theorem DaemonSetsController.updateDaemonSet.wp_proof
    (wp_manage : DaemonSetsController.manage.spec (GF := GF) (hG := hG))
    (wp_rollingUpdate : DaemonSetsController.rollingUpdate.spec (GF := GF) (hG := hG))
    (wp_cleanupHistory : DaemonSetsController.cleanupHistory.spec (GF := GF) (hG := hG))
    (wp_SatisfiedExpectations : ControllerExpectations.SatisfiedExpectations.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.updateDaemonSet.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
