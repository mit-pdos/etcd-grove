/-
## `(*Reservation).Delay()`: assumed

**Users.** client-go's bucket rate limiter. **Assumed** (`rate.go:139-159`, `DelayFrom(time.Now())`):
`InfDuration` (`MaxInt64`) if the reservation is not OK, else the time to act minus now, or `0`.
**Changes.** From `specs-ref`'s `Reservation__Delay.lean`. **Margin.** None.
-/
module

public import Spec.golang_org.x.time.rate.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rate

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **A non-negative duration.** -/
def Reservation.Delay.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ reservationOk r }}
    (App (Val (r @!! go.GoType.PointerType golang_org.x.time.rate.Reservation.ty @!! go!"Delay")) (Val #()))
  {{ (d : _root_.Perennial.time.Duration), RET #d; ⌜0 ≤ sint.Z d⌝ }}

end spec
end Rate
end EtcdGrove
end Perennial
