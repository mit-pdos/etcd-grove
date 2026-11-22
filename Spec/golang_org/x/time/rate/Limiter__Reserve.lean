/-
`(*rate.Limiter).Reserve()` (prove-metrics-float, 2026-11-22: proved over the real code, until then
the trust boundary). Lean-first; for client-go's bucket rate limiter (`k8s.io/client-go/util/workqueue`, `TypedBucketRateLimiter.When`).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- `rate.reservationOk`'s fact, raw: read-only `ok` and `timeToAct` fields (prove-smalllibs,
2026-11-20: until then opaque; `Reservation.Delay` is proved over the real code). True of what
`Reserve` returns (x/time/rate v0.16.0, `rate.go:227-230`): `ReserveN` returns `&r`, a fresh copy
of `reserveN`'s result, which the limiter does not keep, and no method writes a reservation's
`ok` or `timeToAct` (`CancelAt` writes only the limiter's fields). -/
def rate.reservationRaw (r : Loc) : IProp GF :=
  iprop(∃ (ok : Bool) (tta : _root_.Perennial.time.Time),
    r.[golang_org.x.time.rate.Reservation, go!"ok"] ↦□ ok ∗
    r.[golang_org.x.time.rate.Reservation, go!"timeToAct"] ↦□ tta)

/-- **`r` is a reservation** (persistent): what `Limiter.Reserve` returns. -/
def rate.reservationOk (r : Loc) : IProp GF := iprop(□ rate.reservationRaw r)

instance rate.reservationOk_persistent (r : Loc) :
    Persistent (rate.reservationOk (GF := GF) r) := by
  unfold rate.reservationOk; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **`rl.Reserve()`** on a rate limiter: a reservation (`ReserveN(time.Now(), 1)`, under the
limiter's own mutex: safe for concurrent use). -/
abbrev rate.Limiter.Reserve.spec : Prop :=
  ∀ (rl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ rate.limiterOk rl }}
    (App (Val (rl @!! go.GoType.PointerType rate.Limiter.ty @!! go!"Reserve")) (Val #()))
  {{ (r : Loc), RET #r; rate.reservationOk r }}

end spec

end EtcdGrove
end Perennial
