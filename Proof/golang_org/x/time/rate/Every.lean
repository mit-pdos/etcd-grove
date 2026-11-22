/-
Proof of `Spec/golang_org/x/time/rate/Every.lean` over the real code (x/time/rate v0.16.0,
`rate.go:25-30`; prove-metrics3, 2026-11-21: until then a trust-boundary axiom): `Inf` for
`interval <= 0`, else `1 / Limit(interval.Seconds())`, a float division, which does not panic.
-/
module

public import Spec.golang_org.x.time.rate.Every
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

theorem rate.Every.wp_proof
    (wp_Seconds : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG)) :
    rate.Every.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start as -
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; itrivial
  · wp_apply wp_Seconds $$ [$interval] as %f interval
    (try wp_auto)
    wp_apply wp_float64_div as %_ -
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
