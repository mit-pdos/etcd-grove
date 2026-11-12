/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/IsPodTerminal.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodTerminal
public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodPhaseTerminal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

theorem IsPodTerminal.wp_proof
    (wp_IsPodPhaseTerminal : IsPodPhaseTerminal.spec (GF := GF) (hG := hG)) :
    IsPodTerminal.spec (GF := GF) (hG := hG) := by
  intro pod dq d
  wp_start as Hp
  iunfold podAt at Hp
  icases Hp with ⟨%v, Hl, Hd⟩
  icases pod_phase_eq v dq d $$ Hd with ⟨Hd, %Hph⟩
  wp_auto
  icases (Access.access
      (A := pod.[k8s_io.api.core.v1.Pod, go!"Status"].[k8s_io.api.core.v1.PodStatus, go!"Phase"] ↦{dq}
        v.Status'.Phase')
      (A' := pod.[k8s_io.api.core.v1.Pod, go!"Status"].[k8s_io.api.core.v1.PodStatus, go!"Phase"] ↦{dq}
        v.Status'.Phase')
      (P := pod ↦{dq} v)) $$ Hl with ⟨Hf, Hl⟩
  wp_auto
  ihave Hl := Hl $$ Hf
  wp_apply (wp_IsPodPhaseTerminal v.Status'.Phase')
  rw [Hph]
  iapply HΦ
  iunfold podAt
  iexists v
  iframe

end proof

end dsctl
end EtcdGrove
end Perennial
