/-
The proof of `Spec/google_golang_org/grpc/internal/status/IsRestrictedControlPlaneCode.lean`: the code
(`Status.Code`'s spec), then the switch.
-/
module

public import Spec.google_golang_org.grpc.internal.status.IsRestrictedControlPlaneCode

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.status.Assumptions]

theorem istatus.IsRestrictedControlPlaneCode.wp_proof :
    istatus.IsRestrictedControlPlaneCode.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start as #Hs
  wp_auto
  wp_apply Hs
  by_cases hm : c ∈ grpcHdr.restrictedCodes
  · rw [show decide (c ∈ grpcHdr.restrictedCodes) = true by simp [hm]]
    simp only [grpcHdr.restrictedCodes, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (wp_auto; iapply HΦ; itrivial)
  · rw [show decide (c ∈ grpcHdr.restrictedCodes) = false by simp [hm]]
    simp only [grpcHdr.restrictedCodes, List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hm
    repeat (first | wp_auto | simp only [h1, h2, h3, h4, h5, h6, h7, decide_false])
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
