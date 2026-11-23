/-
Proof of `Spec/golang_org/x/time/rate/Limit__tokensFromDuration.lean` over the real code (x/time/rate
v0.16.0, `rate.go:451-456`; prove-metrics-float, 2026-11-22, as a lemma of `reserveN`'s proof; its own
file since rate-wait, 2026-11-23, for `CancelAt`).
-/
module

public import Spec.golang_org.x.time.rate.Limit__tokensFromDuration
public import Spec.time.Duration__Seconds_ptr

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

theorem rate.Limit.tokensFromDuration.wp_proof
    (wp_Seconds : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG)) :
    rate.Limit.tokensFromDuration.spec (GF := GF) (hG := hG) := by
  intro l d
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  wp_start as -
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  generalize float64Leb l (W64 0) = c
  cases c
  · wp_auto
    wp_apply wp_Seconds $$ [$d] as %f d
    wp_apply wp_float64_mul as %g -
    iapply HΦ; itrivial
  · wp_auto
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
