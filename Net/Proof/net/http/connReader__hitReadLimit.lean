/-
The proof of `connReader.hitReadLimit` (`Net/Spec/net/http/connReader__hitReadLimit.lean`).
-/
module

public import Net.Spec.net.http.connReader__hitReadLimit

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

theorem connReader.hitReadLimit.wp_proof : connReader.hitReadLimit.spec (GF := GF) (hG := hG) := by
  intro cr dq v
  wp_start as Hr
  wp_auto
  have h : sint.Z (W64 0) = 0 := rfl
  rw [h]
  iapply HΦ
  iexact Hr

end proof

end net.http
end Perennial
