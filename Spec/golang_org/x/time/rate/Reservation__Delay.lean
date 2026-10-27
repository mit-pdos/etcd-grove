/-
`(*rate.Reservation).Delay()`: the trust boundary (`golang.org/x/time/rate` is names-only). Lean-first;
for client-go's bucket rate limiter.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Reserve

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`r.Delay()`**: a non-negative duration (`DelayFrom(time.Now())`: `InfDuration`, `MaxInt64`, if
the reservation is not OK, else the time to act minus now, or `0` if that is negative; x/time/rate
v0.16.0, `rate.go:139-159`). -/
abbrev rate.Reservation.Delay.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ rate.reservationOk r }}
    (App (Val (r @!! go.GoType.PointerType rate.Reservation.ty @!! go!"Delay")) (Val #()))
  {{ (d : _root_.Perennial.time.Duration), RET #d; ⌜0 ≤ sint.Z d⌝ }}

end spec

end EtcdGrove
end Perennial
