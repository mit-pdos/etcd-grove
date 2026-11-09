/-
## `(*Limiter).Reserve()`: assumed

**Users.** client-go's `TypedBucketRateLimiter.When` (Kubernetes). **Assumed** (`rate.go:183-187`,
`ReserveN(time.Now(), 1)` under the mutex). **Changes.** From `specs-ref`'s `Limiter__Reserve.lean`.
**Margin.** None.
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

/-- **A reservation.** -/
def Limiter.Reserve.spec : Prop :=
  ∀ (rl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ limiterOk rl }}
    (App (Val (rl @!! go.GoType.PointerType golang_org.x.time.rate.Limiter.ty @!! go!"Reserve")) (Val #()))
  {{ (r : Loc), RET #r; reservationOk r }}

end spec
end Rate
end EtcdGrove
end Perennial
