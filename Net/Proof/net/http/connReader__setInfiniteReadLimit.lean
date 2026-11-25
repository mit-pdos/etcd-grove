/-
The proof of `connReader.setInfiniteReadLimit` (`Net/Spec/net/http/connReader__setInfiniteReadLimit.lean`).
-/
module

public import Net.Spec.net.http.connReader__setInfiniteReadLimit

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

theorem connReader.setInfiniteReadLimit.wp_proof :
    connReader.setInfiniteReadLimit.spec (GF := GF) (hG := hG) := by
  intro cr v
  wp_start as Hr
  wp_auto
  have h : W64 (2 ^ 63 - 1) = W64 9223372036854775807 := rfl
  rw [h]
  iapply HΦ
  iexact Hr

end proof

end net.http
end Perennial
