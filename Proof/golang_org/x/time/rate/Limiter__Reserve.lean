/-
Proof of `Spec/golang_org/x/time/rate/Limiter__Reserve.lean` over the real code (x/time/rate v0.16.0,
`rate.go:207-230`: `Reserve` is `ReserveN(time.Now(), 1)`, which returns `&r` of `reserveN`'s
result; prove-metrics-float, 2026-11-22: until then a trust-boundary axiom, the token bucket's
`-tokens` not stepped before Perennial's IEEE 754 floats). Lean-first.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Reserve
public import Spec.golang_org.x.time.rate.Limiter__reserveN
public import Perennial.Spec.time.Now

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

theorem rate.Limiter.Reserve.wp_proof
    (wp_Now : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (wp_reserveN : rate.Limiter.reserveN.spec (GF := GF) (hG := hG)) :
    rate.Limiter.Reserve.spec (GF := GF) (hG := hG) := by
  intro rl
  wp_start as #Hl
  iapply wp_fupd
  wp_auto
  wp_apply wp_Now as %now -
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_reserveN $$ [$Hpkg $Hl] as %r %Hr
  iStructNamed r
  ipersist ok
  ipersist timeToAct
  imodintro
  iapply HΦ
  iunfold rate.reservationOk
  imodintro
  iunfold rate.reservationRaw
  iexists r.ok', r.timeToAct'
  isplitl
  · iexact ok
  · iexact timeToAct

end proof

end EtcdGrove
end Perennial
