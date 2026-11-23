/-
The proof of `httpguts.HeaderValuesContainsToken`
(`Net/Spec/vendor/golang_org/x/net/http/httpguts/HeaderValuesContainsToken.lean`): the range over no
values runs no iteration.
-/
module

public import Net.Spec.vendor.golang_org.x.net.http.httpguts.HeaderValuesContainsToken

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace vendor.golang_org.x.net.http.httpguts

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : vendor.golang_org.x.net.http.httpguts.Assumptions]

theorem HeaderValuesContainsToken.wp_proof :
    HeaderValuesContainsToken.spec (GF := GF) (hG := hG) := by
  intro values token
  wp_start as %Hlen
  wp_auto
  ihave HI : (i_ptr ↦ W64 0 : IProp GF) $$ [i]
  · iexact i
  wp_for HI
  rw [Hlen]
  rw [decide_eq_false (Int.lt_irrefl _)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_auto
  iapply HΦ; itrivial

end proof

end vendor.golang_org.x.net.http.httpguts
end Perennial
