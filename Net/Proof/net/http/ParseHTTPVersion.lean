/-
The proof of `ParseHTTPVersion` (`Net/Spec/net/http/ParseHTTPVersion.lean`): the switch's two cases.
-/
module

public import Net.Spec.net.http.ParseHTTPVersion

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

theorem ParseHTTPVersion.wp_proof : ParseHTTPVersion.spec (GF := GF) (hG := hG) := by
  intro vers
  wp_start as %Hv
  wp_auto
  rcases Hv with rfl | rfl
  all_goals
    simp (config := { decide := true }) only [↓reduceIte]
    wp_auto
    try simp (config := { decide := true }) only [↓reduceIte]
    try wp_auto
    iapply HΦ; itrivial

end proof

end net.http
end Perennial
