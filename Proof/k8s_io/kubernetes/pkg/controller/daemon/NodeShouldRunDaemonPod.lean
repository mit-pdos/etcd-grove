/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/NodeShouldRunDaemonPod.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: the template's affinity read, `NewRequiredNodeAffinity`, `daemonPodTolerations`, `nodeShouldRunDaemonPod` (its `rnaOk`).

Still to add as hypotheses (callees without a spec yet): `nodeaffinity.NewRequiredNodeAffinity` (track B's `rnaOk`: its spec is in B's `nodeShouldRunDaemonPod` proof's callees).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.NodeShouldRunDaemonPod
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.daemonPodTolerations
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.nodeShouldRunDaemonPod

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

theorem NodeShouldRunDaemonPod.wp_proof
    (wp_daemonPodTolerations : daemonPodTolerations.spec (GF := GF) (hG := hG))
    (wp_nodeShouldRunDaemonPod : nodeShouldRunDaemonPod.spec (GF := GF) (hG := hG)) :
    NodeShouldRunDaemonPod.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
