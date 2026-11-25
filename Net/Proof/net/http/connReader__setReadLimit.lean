/-
The proof of `connReader.setReadLimit` (`Net/Spec/net/http/connReader__setReadLimit.lean`).
-/
module

public import Net.Spec.net.http.connReader__setReadLimit

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

theorem connReader.setReadLimit.wp_proof : connReader.setReadLimit.spec (GF := GF) (hG := hG) := by
  intro cr v remain
  wp_start as Hr
  wp_auto
  iapply HΦ
  iexact Hr

end proof

end net.http
end Perennial
