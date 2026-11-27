/-
The proof of `validMethod` (`Net/Spec/net/http/validMethod.lean`): `isToken`.
-/
module

public import Net.Spec.net.http.validMethod
public import Net.Spec.net.http.isToken

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

theorem validMethod.wp_proof (wp_isToken : isToken.spec (GF := GF) (hG := hG)) :
    validMethod.spec (GF := GF) (hG := hG) := by
  intro method
  wp_start as #Htab
  wp_auto
  wp_apply wp_isToken
  all_goals try iexact Htab
  iapply HΦ; itrivial

end proof

end net.http
end Perennial
