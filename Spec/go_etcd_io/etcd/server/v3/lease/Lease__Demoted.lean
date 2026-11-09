/-
## `(*Lease).Demoted()` (`lease.go:99`): names only (an assumed spec)

**Users.** 2c's `leaseTimeToLive` (`v3_server.go:662`: `ErrLeaderChanged` when the lessor was
demoted during the lookup). Any goroutine.

**Why it is true.** `l.expiryMu.RLock()`; `l.expiry == forever` (a `time.Time` comparison);
`RUnlock`. Untranslated (the struct comparison of `time.Time`), so assumed.

**Changes** (new: no old spec; 2c's sketch reads it). **Margin.** The value (the expiry, time).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Whether the object's expiry is `forever`** (any goroutine): some boolean. -/
def Lease.Demoted.spec : Prop :=
  ∀ (γ : Names) (l : Loc) (id ttl : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseObj γ l id ttl }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"Demoted")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec
end Lease
end EtcdGrove
end Perennial
