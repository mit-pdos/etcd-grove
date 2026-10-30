/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/IsPodPhaseTerminal.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodPhaseTerminal

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

theorem IsPodPhaseTerminal.wp_proof : IsPodPhaseTerminal.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show phaseTerminalB _ = true by decide]
    iapply HΦ; itrivial
  · rw [show phaseTerminalB p = decide (p = go!"Succeeded") by simp [phaseTerminalB, Hif]]
    iapply HΦ; itrivial

end proof

end dsctl
end EtcdGrove
end Perennial
