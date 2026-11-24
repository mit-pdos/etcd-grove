/-
The proof of `modelLowerASCII` (`Net/Spec/net/http/modelLowerASCII.lean`).
-/
module

public import Net.Spec.net.http.modelLowerASCII

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelLowerASCII.wp_proof : modelLowerASCII.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  wp_auto
  all_goals repeat (first | wp_if_destruct | wp_auto)
  · rw [show lowerASCII b = b + W8 32 by
      unfold lowerASCII; rw [if_pos ⟨by word, by word⟩]]
    iapply HΦ; itrivial
  · rw [show lowerASCII b = b by
      unfold lowerASCII; rw [if_neg (fun h => Hif (by have := h.2; word))]]
    iapply HΦ; itrivial
  · rw [show lowerASCII b = b by
      unfold lowerASCII; rw [if_neg (fun h => Hif (by have := h.1; word))]]
    iapply HΦ; itrivial

end proof

end net.http
end Perennial
