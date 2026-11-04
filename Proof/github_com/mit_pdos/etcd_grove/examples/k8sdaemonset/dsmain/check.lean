/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/dsmain/check.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: `List`'s atomic update fired from `s1Reader` (S1 at the listed state: the
pods' table of namespace `default`), then the loop with the map `bound` holding the target nodes
of the pods of `uid` seen so far (no pod twice: S1).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__CoreV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.coreV1__Pods
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.podClient__List
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.controlledBy
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.util.GetTargetNodeName

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI Iris.ProofMode apimodel dsctl informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]
variable [util_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

theorem check.wp_proof
    (wp_CoreV1 : apimodel.Clientset.CoreV1.spec (GF := GF) (hG := hG))
    (wp_Pods : apimodel.coreV1.Pods.spec (GF := GF) (hG := hG))
    (wp_PodList : apimodel.podClient.List.spec (GF := GF) (hG := hG))
    (wp_controlledBy : dsmain.controlledBy.spec (GF := GF) (hG := hG))
    (wp_GetTargetNodeName : dsctl.GetTargetNodeName.spec (GF := GF) (hG := hG)) :
    check.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsmain
end EtcdGrove
end Perennial
