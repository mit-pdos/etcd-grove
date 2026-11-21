/-
Proof of `Spec/golang_org/x/time/rate/Reservation__Delay.lean` over the real code (x/time/rate
v0.16.0, `rate.go:139-159`, `Delay` and the `DelayFrom` it calls; prove-smalllibs, 2026-11-20:
until then a trust-boundary axiom): `InfDuration` (`MaxInt64`) if the reservation is not OK, else
`timeToAct.Sub(now)`, or `0` if that is negative.
-/
module

public import Spec.golang_org.x.time.rate.Reservation__Delay
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Sub

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

theorem rate.Reservation.Delay.wp_proof
    (wp_Now : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (wp_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG)) :
    rate.Reservation.Delay.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as Hr
  iunfold rate.reservationOk at Hr
  iunfold rate.reservationRaw at Hr
  icases Hr with ⟨%ok, %tta, #Hok, #Htta⟩
  wp_auto
  wp_apply wp_Now as %now -
  wp_method_call
  wp_call
  cases ok
  · wp_auto
    rw [show golang_org.x.time.rate.InfDuration = #(W64 9223372036854775807) from rfl]
    wp_auto
    iapply HΦ
    ipureintro
    decide
  wp_auto
  -- `(*Time).Sub` of `&r.timeToAct`: the value method on the field's (read-only) value
  wp_method_call
  wp_call
  wp_load
  wp_apply wp_Sub as %d -
  wp_if_destruct
  · iapply HΦ
    ipureintro
    decide
  · iapply HΦ
    ipureintro
    word

end proof

end EtcdGrove
end Perennial
