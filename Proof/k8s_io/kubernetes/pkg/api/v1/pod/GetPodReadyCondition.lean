/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/GetPodReadyCondition.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.GetPodReadyCondition
public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.GetPodCondition

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

theorem GetPodReadyCondition.wp_proof
    (wp_GetPodCondition : GetPodCondition.spec (GF := GF) (hG := hG)) :
    GetPodReadyCondition.spec (GF := GF) (hG := hG) := by
  intro sv dq cs
  wp_start as Hs
  wp_auto
  wp_apply (wp_GetPodCondition status_ptr (DFrac.own 1) sv dq cs go!"Ready") $$ [$status $Hs]
    as %i %p ⟨status, Hs, %Hr⟩
  iapply HΦ
  iframe
  ipureintro; exact ⟨i, Hr⟩

end proof

end dsctl
end EtcdGrove
end Perennial
