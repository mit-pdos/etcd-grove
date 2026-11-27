/-
The proof of `isToken` (`Net/Spec/net/http/isToken.lean`): httpguts' `ValidHeaderFieldName`.
-/
module

public import Net.Spec.net.http.isToken
public import Net.Spec.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName

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

theorem isToken.wp_proof
    (wp_VHFN : vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName.spec (GF := GF) (hG := hG)) :
    isToken.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start as #Htab
  wp_auto
  wp_apply wp_VHFN
  all_goals try iexact Htab
  iapply HΦ; itrivial

end proof

end net.http
end Perennial
