/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/RealPodControl__DeletePod.lean`, over gap D2's
body hypothesis (`RealPodControl__DeletePod_body.lean`). Lean-first; Stage 3 of the autoverify
run (track B): a stub (as `RealPodControl__createPods.lean`'s proof, through the clientset's
`CoreV1().Pods(ns).Delete`, `deleteAU` fired at the model's linearization point). Callee
hypotheses still to add: `meta.Accessor`, `apierrors.IsNotFound`, `logr`'s `V`/`Info`, `KObj`,
the recorder's `Eventf` (`recorderOk`).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.RealPodControl__DeletePod
public import Spec.k8s_io.kubernetes.pkg.controller.RealPodControl__DeletePod_body
public import Spec.fmt.Errorf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__CoreV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.coreV1__Pods
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.podClient__Delete

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.kubernetes.pkg.controller

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

theorem RealPodControl.DeletePod.wp_proof
    (h_body : RealPodControl.DeletePod_body.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_CoreV1 : apimodel.Clientset.CoreV1.spec (GF := GF) (hG := hG))
    (wp_Pods : apimodel.coreV1.Pods.spec (GF := GF) (hG := hG))
    (wp_Delete : apimodel.podClient.Delete.spec (GF := GF) (hG := hG)) :
    RealPodControl.DeletePod.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
