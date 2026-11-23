/-
The proof of `shouldClose` (`Net/Spec/net/http/shouldClose.lean`): no `Connection` header.
-/
module

public import Net.Spec.net.http.shouldClose
public import Net.Spec.net.http.Header__Del
public import Net.Spec.vendor.golang_org.x.net.http.httpguts.HeaderValuesContainsToken

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

theorem shouldClose.wp_proof
    (wp_HVCT : vendor.golang_org.x.net.http.httpguts.HeaderValuesContainsToken.spec (GF := GF) (hG := hG)) :
    shouldClose.spec (GF := GF) (hG := hG) := by
  intro major minor h rm
  wp_start as Hm
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; iexact Hm
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) h _
    go!"Connection" _) $$ Hm as Hm
  try wp_auto
  wp_apply wp_HVCT
  · ipureintro; rfl
  try wp_auto
  all_goals
    repeat (first | wp_if_destruct | (wp_apply wp_HVCT; ipureintro; rfl) | wp_auto)
  all_goals (iapply HΦ; iexact Hm)

end proof

end net.http
end Perennial
