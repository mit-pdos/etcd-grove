/-
## `rate.Every(d)`: assumed

**Users.** `Transport.Start` (`rafthttp/transport.go:153`, the default dial-retry rate).
**Assumed** (`rate.go:44-50`): `Inf` for `d ≤ 0`, else `1 / d.Seconds()`; a float. **Changes.**
From `specs-ref`'s `Every.lean`. **Margin.** The value is not stated.
-/
module

public import SpecPlan.Spec.golang_org.x.time.rate.Api

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

/-- `rate.Every(d)` returns some limit (a `float64`'s bits). -/
def Every.spec : Prop :=
  ∀ (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
    (App (Val (@! golang_org.x.time.rate.Every)) (Val #d))
  {{ (l : w64), RET #l; True }}

end spec
end Rate
end EtcdGrove
end Perennial
