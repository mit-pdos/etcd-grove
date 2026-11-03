/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__constructHistory.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__constructHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.revisionClient__Update
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__controlledHistories
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__dedupCurHistories
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__snapshot
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.Match
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.maxRevision

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

theorem DaemonSetsController.constructHistory.wp_proof
    (wp_controlledHistories : DaemonSetsController.controlledHistories.spec (GF := GF) (hG := hG))
    (wp_Match : Match.spec (GF := GF) (hG := hG))
    (wp_maxRevision : maxRevision.spec (GF := GF) (hG := hG))
    (wp_snapshot : DaemonSetsController.snapshot.spec (GF := GF) (hG := hG))
    (wp_dedupCurHistories : DaemonSetsController.dedupCurHistories.spec (GF := GF) (hG := hG))
    (wp_Update : apimodel.revisionClient.Update.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.constructHistory.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
