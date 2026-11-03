/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/predicates.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

`RequiredNodeAffinity.Match` is gap D2's (`RequiredNodeAffinity__Match_body.lean`): its spec (over `rnaOk`) is still to write, a callee hypothesis to add.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.predicates
public import Spec.k8s_io.component_helpers.scheduling.corev1.FindMatchingUntoleratedTaint

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

theorem predicates.wp_proof
    (wp_FindMatchingUntoleratedTaint : FindMatchingUntoleratedTaint.spec (GF := GF) (hG := hG)) :
    predicates.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
