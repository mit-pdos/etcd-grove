/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/IsPodReadyConditionTrue.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodReadyConditionTrue
public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.GetPodReadyCondition

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

theorem IsPodReadyConditionTrue.wp_proof
    (wp_GetPodReadyCondition : GetPodReadyCondition.spec (GF := GF) (hG := hG)) :
    IsPodReadyConditionTrue.spec (GF := GF) (hG := hG) := by
  intro sv dq cs
  wp_start as Hs
  wp_auto
  wp_apply (wp_GetPodReadyCondition sv dq cs) $$ [$Hs] as %p ⟨Hs, %Hr⟩
  obtain ⟨i, Hr⟩ := Hr
  unfold condResult at Hr
  cases hf : condFind cs go!"Ready" with
  | none =>
    rw [hf] at Hr
    obtain ⟨-, rfl⟩ := Hr
    wp_auto
    have hb : podReadyB cs = false := by simp [podReadyB, hf]
    rw [hb]
    iapply HΦ; iexact Hs
  | some jc =>
    obtain ⟨j, c⟩ := jc
    rw [hf] at Hr
    obtain ⟨-, rfl⟩ := Hr
    obtain ⟨hc, -⟩ := condFind_lookup _ cs j c hf
    icases ownSliceD_elem_acc _ _ _ _ j c hc $$ Hs with ⟨%v, Hv, Hown, Hcl⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hv with ⟨Hv, %Hnn⟩
    ihave %Hst : ⌜v.Status' = c.Status'⌝ $$ [Hown]
    · iunfold kd.core.PodCondition.own at Hown
      icases Hown with ⟨-, -, %h, -⟩
      ipureintro; exact h
    rw [decide_eq_false Hnn]
    wp_auto
    icases (AccessStrict.access_strict
        (A := (sliceIndexRef k8s_io.api.core.v1.PodCondition (j : Int) sv.Conditions').[
          k8s_io.api.core.v1.PodCondition, go!"Status"] ↦{dq} v.Status')
        (A' := (sliceIndexRef k8s_io.api.core.v1.PodCondition (j : Int) sv.Conditions').[
          k8s_io.api.core.v1.PodCondition, go!"Status"] ↦{dq} v.Status')
        (P := sliceIndexRef k8s_io.api.core.v1.PodCondition (j : Int) sv.Conditions' ↦{dq} v))
      $$ Hv with ⟨Hf, Hv⟩
    wp_auto
    ihave Hv := Hv $$ Hf
    have hb : podReadyB cs = decide (v.Status' = go!"True") := by simp [podReadyB, hf, Hst]
    rw [hb]
    iapply HΦ
    iapply Hcl $$ Hv Hown

end proof

end dsctl
end EtcdGrove
end Perennial
