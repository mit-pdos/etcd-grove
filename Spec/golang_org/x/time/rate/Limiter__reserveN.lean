/-
`(*rate.Limiter).reserveN(t, n, maxFutureReserve)`: the token bucket of `Reserve` (and of `Wait`,
`Allow`). Lean-first; prove-metrics-float (2026-11-22): proved over the real code, with Perennial's
IEEE 754 floats.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **`rl.reserveN(t, n, maxFutureReserve)`** on a rate limiter, for any time, count and maximum
wait: a reservation (a `Reservation` value) of `rl` (its `lim` field), taken under the limiter's
own mutex (x/time/rate v0.16.0, `rate.go:380-428`: the limiter's `limit`, `burst` and `tokens`
are any values, NaN and infinities included, and no float operation or conversion of the bucket
panics in Go). -/
abbrev rate.Limiter.reserveN.spec : Prop :=
  ∀ (rl : Loc) (t : _root_.Perennial.time.Time) (n : w64) (mfr : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ rate.limiterOk rl }}
    (App (App (App (Val (rl @!! go.GoType.PointerType rate.Limiter.ty
        @!! go!"reserveN"))
      (Val #t)) (Val #n)) (Val #mfr))
  {{ (r : golang_org.x.time.rate.Reservation), RET #r; ⌜r.lim' = rl⌝ }}

end spec

end EtcdGrove
end Perennial
