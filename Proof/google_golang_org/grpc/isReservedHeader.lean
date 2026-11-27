/-
The proof of `Spec/google_golang_org/grpc/isReservedHeader.lean`: the first byte, then the switch.
-/
module

public import Spec.google_golang_org.grpc.isReservedHeader

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
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.isReservedHeader.wp_proof : grpc.isReservedHeader.spec (GF := GF) (hG := hG) := by
  intro h
  wp_start as -
  wp_auto
  wp_if_destruct
  · rw [show decide (grpcHdr.reservedHdr []) = false by decide]
    iapply HΦ
    itrivial
  obtain ⟨b, t, rfl⟩ : ∃ b t, h = b :: t := by
    cases h with
    | nil => exact absurd rfl Hif
    | cons b t => exact ⟨b, t, rfl⟩
  simp only [List.getElem?_cons_zero]
  wp_auto
  wp_if_destruct
  · rw [show decide (grpcHdr.reservedHdr (W8 58 :: t)) = true by simp [grpcHdr.reservedHdr]]
    iapply HΦ
    itrivial
  · by_cases hm : b :: t ∈ grpcHdr.reservedHdrs
    · rw [show decide (grpcHdr.reservedHdr (b :: t)) = true by simp [grpcHdr.reservedHdr, hm]]
      simp only [grpcHdr.reservedHdrs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
      rcases hm with h | h | h | h | h | h | h | h <;>
        (simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h; wp_auto; iapply HΦ; itrivial)
    · rw [show decide (grpcHdr.reservedHdr (b :: t)) = false by
        simpa [grpcHdr.reservedHdr, hm] using Hif]
      simp only [grpcHdr.reservedHdrs, List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hm
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hm
      repeat (first | wp_auto | simp only [h1, h2, h3, h4, h5, h6, h7, h8, decide_false])
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
