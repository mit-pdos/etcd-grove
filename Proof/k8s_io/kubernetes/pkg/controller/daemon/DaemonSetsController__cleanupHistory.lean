/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__cleanupHistory.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__cleanupHistory
public import Spec.fmt.Errorf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.revisionClient__Delete
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__getNodesToDaemonPods
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.historiesByRevision__Len
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.historiesByRevision__Less
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.historiesByRevision__Swap

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

theorem DaemonSetsController.cleanupHistory.wp_proof
    (wp_getNodesToDaemonPods : DaemonSetsController.getNodesToDaemonPods.spec (GF := GF) (hG := hG))
    (wp_hLen : historiesByRevision.Len.spec (GF := GF) (hG := hG))
    (wp_hLess : historiesByRevision.Less.spec (GF := GF) (hG := hG))
    (wp_hSwap : historiesByRevision.Swap.spec (GF := GF) (hG := hG))
    (wp_CRDelete : apimodel.revisionClient.Delete.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.cleanupHistory.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
