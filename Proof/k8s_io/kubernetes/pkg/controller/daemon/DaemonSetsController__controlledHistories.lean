/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__controlledHistories.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

The namespace lister's `List` (`controllerRevisionNamespaceLister__List`) and `labels.Everything` are hypotheses to add.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__controlledHistories
public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.LabelSelectorAsSelector
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerRevisionControllerRefManager__ClaimControllerRevisions
public import Spec.k8s_io.kubernetes.pkg.controller.NewControllerRevisionControllerRefManager
public import Spec.k8s_io.kubernetes.pkg.controller.RecheckDeletionTimestamp

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

theorem DaemonSetsController.controlledHistories.wp_proof
    (wp_LabelSelectorAsSelector : labels.LabelSelectorAsSelector.spec (GF := GF) (hG := hG))
    (wp_RecheckDeletionTimestamp : RecheckDeletionTimestamp.spec (GF := GF) (hG := hG))
    (wp_NewCRRefManager : NewControllerRevisionControllerRefManager.spec (GF := GF) (hG := hG))
    (wp_ClaimCRs : ControllerRevisionControllerRefManager.ClaimControllerRevisions.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.controlledHistories.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
