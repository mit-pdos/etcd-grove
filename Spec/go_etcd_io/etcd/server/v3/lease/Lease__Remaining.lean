/-
## `(*Lease).Remaining()` (`lease.go:117`)

**Users.** 2c's `leaseTimeToLive` (`v3_server.go:652`: the answer's `TTL`), `leasesByExpiry.Less`
(`Leases`' sort), `Promote`. Any goroutine.

**Proof sketch.** `l.expiryMu.RLock()` (the object's expiry lock: its invariant holds the `expiry`
field at some time value); `IsZero`: `MaxInt64`; else `time.Until(l.expiry)` (Perennial's clock);
`RUnlock`.

**Changes** (from `specs-ref`'s `Lease__Remaining.lean`): over `leaseObj`. **Margin.** The value
(time is not modelled; W0's time-to-live allows any `TTL`).
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

/-- **The object's remaining time** (any goroutine): some duration. -/
def Lease.Remaining.spec : Prop :=
  ∀ (γ : Names) (l : Loc) (id ttl : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseObj γ l id ttl }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"Remaining")) (Val #()))
  {{ (d : time.Duration), RET #d; True }}

end spec
end Lease
end EtcdGrove
end Perennial
