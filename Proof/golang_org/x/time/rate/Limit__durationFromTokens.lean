/-
Proof of `Spec/golang_org/x/time/rate/Limit__durationFromTokens.lean` over the real code (x/time/rate
v0.16.0, `rate.go:458-471`; prove-metrics-float, 2026-11-22, as a lemma of `reserveN`'s proof; its own
file since rate-wait, 2026-11-23, for `CancelAt`).
-/
module

public import Spec.golang_org.x.time.rate.Limit__durationFromTokens

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

theorem rate.Limit.durationFromTokens.wp_proof :
    rate.Limit.durationFromTokens.spec (GF := GF) (hG := hG) := by
  intro l f
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  wp_start as -
  wp_auto
  rw [show golang_org.x.time.rate.InfDuration = #(W64 9223372036854775807) from rfl]
  generalize float64Leb l (W64 0) = c
  cases c
  case true =>
    wp_auto
    iapply HΦ; itrivial
  case false =>
    wp_auto
    wp_apply wp_float64_div as %q -
    wp_apply wp_float64_mul as %dur -
    generalize (float64Leb (W64 4890909195324358656) dur && !float64Eq dur (W64 4890909195324358656)) = c
    cases c
    case true =>
      wp_auto
      iapply HΦ; itrivial
    case false =>
      wp_auto
      wp_apply wp_ArbitraryInt as %x -
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
