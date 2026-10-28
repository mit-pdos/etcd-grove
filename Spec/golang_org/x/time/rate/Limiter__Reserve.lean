/-
`(*rate.Limiter).Reserve()`: the trust boundary (`golang.org/x/time/rate` is names-only). Lean-first;
for client-go's bucket rate limiter (`k8s.io/client-go/util/workqueue`, `TypedBucketRateLimiter.When`).
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

/-- `rate.reservationOk`'s fact, raw (opaque). -/
opaque rate.reservationRaw (r : Loc) : IProp GF

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
