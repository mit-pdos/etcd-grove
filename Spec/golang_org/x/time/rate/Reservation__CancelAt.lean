/-
`(*rate.Reservation).CancelAt(t)` (x/time/rate v0.16.0, `rate.go:168-203`): `wait`'s cancellation of
its reservation when the context is done first (rate-wait, 2026-11-23). Lean-first.
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

/-- **`r.CancelAt(t)`** of a reservation of the rate limiter `rv.lim'` (read through any fraction of
`r`): returns, having given back to the limiter what it can of the reservation's tokens (under the
limiter's own mutex; the float arithmetic panics nowhere in Go, whatever the values). -/
abbrev rate.Reservation.CancelAt.spec : Prop :=
  ∀ (r : Loc) (rv : golang_org.x.time.rate.Reservation) (dq : DFrac) (t : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ r ↦{dq} rv ∗
      rate.limiterOk rv.lim' }}
    (App (Val (r @!! go.GoType.PointerType golang_org.x.time.rate.Reservation.ty @!! go!"CancelAt"))
      (Val #t))
  {{ RET #(); r ↦{dq} rv }}

end spec

end EtcdGrove
end Perennial
