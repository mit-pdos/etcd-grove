/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/GetPodCondition.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.GetPodCondition

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

theorem GetPodCondition.wp_proof
    (wp_GetPodConditionFromList : GetPodConditionFromList.spec (GF := GF) (hG := hG)) :
    GetPodCondition.spec (GF := GF) (hG := hG) := by
  intro st dq' sv dq cs t
  wp_start as ⟨Hst, Hs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hst with ⟨Hst, %Hnn⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  icases (AccessStrict.access_strict
      (A := st.[k8s_io.api.core.v1.PodStatus, go!"Conditions"] ↦{dq'} sv.Conditions')
      (A' := st.[k8s_io.api.core.v1.PodStatus, go!"Conditions"] ↦{dq'} sv.Conditions')
      (P := st ↦{dq'} sv)) $$ Hst with ⟨Hf, Hst⟩
  wp_auto
  ihave Hst := Hst $$ Hf
  wp_apply (wp_GetPodConditionFromList sv.Conditions' dq cs t) $$ [$Hs] as %i %p ⟨Hs, %Hr⟩
  iapply HΦ
  iframe
  ipureintro; exact Hr

end proof

end dsctl
end EtcdGrove
end Perennial
