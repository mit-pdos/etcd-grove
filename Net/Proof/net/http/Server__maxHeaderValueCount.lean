/-
The proof of `Server.maxHeaderValueCount` (`Net/Spec/net/http/Server__maxHeaderValueCount.lean`).
-/
module

public import Net.Spec.net.http.Server__maxHeaderValueCount

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Server.maxHeaderValueCount.wp_proof : Server.maxHeaderValueCount.spec (GF := GF) (hG := hG) := by
  intro s n dq
  wp_start as Hn
  wp_auto
  by_cases h : 0 < sint.Z n
  · simp only [h, ↓reduceIte]
    wp_if_destruct
    all_goals (try wp_auto)
    · iapply HΦ; iexact Hn
    · exfalso; apply ‹¬ _›; revert h; word
  · simp only [h, ↓reduceIte]
    wp_if_destruct
    all_goals (try wp_auto)
    · exfalso; apply h; revert ‹_ < _›; word
    · iapply HΦ; iexact Hn

end proof

end net.http
end Perennial
