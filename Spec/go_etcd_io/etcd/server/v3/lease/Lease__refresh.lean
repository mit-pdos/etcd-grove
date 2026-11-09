/-
`(*Lease).refresh(extend)` (`lease.go:84`), an internal helper's spec (mirrors the code).
**Users**: `Grant`, `Renew`, `Promote`, under `le.mu`. **Proof sketch**: `getRemainingTTL`,
`time.Now().Add(...)` (wrapping duration arithmetic: no panic), the expiry stored under
`expiryMu` (`leaseExpiry`). **Changes** (from `specs-ref`'s `Lease__refresh.lean`): over
`leaseExpiry`. **Margin**: the new expiry (time).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false
set_option linter.iris.dupNamespace false

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

/-- **Move the object's expiry** to now plus `extend` plus its remaining TTL. -/
def Lease.refresh.spec : Prop :=
  ∀ (l : Loc) (extend : time.Duration) (t r : w64) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseExpiry l ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ttl"] ↦{dq1} t ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"remainingTTL"] ↦{dq2} r }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"refresh")) (Val #extend))
  {{ RET #();
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ttl"] ↦{dq1} t ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"remainingTTL"] ↦{dq2} r }}

end spec
end Lease
end EtcdGrove
end Perennial
