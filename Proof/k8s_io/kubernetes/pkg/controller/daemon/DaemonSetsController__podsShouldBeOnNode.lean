/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__podsShouldBeOnNode.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

`nodeShouldRunDaemonPod`, the map lookup; in the `shouldContinueRunning` branch every pod is running (`sceneOk` through `podsView`), so the surge create is not reached.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__podsShouldBeOnNode
public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodReady
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.nodeShouldRunDaemonPod
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.podByCreationTimestampAndPhase__Len
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.podByCreationTimestampAndPhase__Less
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.podByCreationTimestampAndPhase__Swap
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.util.AllowsSurge

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

theorem DaemonSetsController.podsShouldBeOnNode.wp_proof
    (wp_nodeShouldRunDaemonPod : nodeShouldRunDaemonPod.spec (GF := GF) (hG := hG))
    (wp_AllowsSurge : AllowsSurge.spec (GF := GF) (hG := hG))
    (wp_IsPodReady : IsPodReady.spec (GF := GF) (hG := hG))
    (wp_podLen : podByCreationTimestampAndPhase.Len.spec (GF := GF) (hG := hG))
    (wp_podLess : podByCreationTimestampAndPhase.Less.spec (GF := GF) (hG := hG))
    (wp_podSwap : podByCreationTimestampAndPhase.Swap.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.podsShouldBeOnNode.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
