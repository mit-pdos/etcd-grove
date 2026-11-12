/-
`(*Lease).getRemainingTTL()` (`lease.go:76`), an internal helper's spec (mirrors the code).
**Users**: `refresh`, `scheduleCheckpointIfNeeded`, under `le.mu`. **Proof sketch**: two field
loads. **Changes** (from `specs-ref`'s `Lease__getRemainingTTL.lean`): unchanged. **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Internal

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

/-- **The checkpointed remaining TTL if set (positive), else the TTL.** -/
def Lease.getRemainingTTL.spec : Prop :=
  ∀ (l : Loc) (t r : w64) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ttl"] ↦{dq1} t ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"remainingTTL"] ↦{dq2} r }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"getRemainingTTL")) (Val #()))
  {{ RET #(if 0 < sint.Z r then r else t);
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"ttl"] ↦{dq1} t ∗
      l.[go_etcd_io.etcd.server.v3.lease.Lease, go!"remainingTTL"] ↦{dq2} r }}

end spec
end Lease
end EtcdGrove
end Perennial
