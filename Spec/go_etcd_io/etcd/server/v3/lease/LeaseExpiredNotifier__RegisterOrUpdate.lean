/-
`(*LeaseExpiredNotifier).RegisterOrUpdate(item)` (`lease_queue.go:83`), an internal helper's spec
(mirrors the code). **Users**: `Grant`, `Renew`, `Promote`, `expireExists`, under `le.mu`. **Proof
sketch**: the map's cell for the id: its time from `item`, `heap.Fix` at its index; else
`heap.Push` (`LeaseQueue.Push.spec`) and the map entry. **Changes** (from `specs-ref`'s
`LeaseExpiredNotifier__RegisterOrUpdate.lean`): unchanged. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

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

/-- **Register lease `id`'s expiry cell, or move the registered one.** -/
def LeaseExpiredNotifier.RegisterOrUpdate.spec : Prop :=
  ∀ (np item : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      notifierAt np (DFrac.own 1) ∗ lwtAt item id (DFrac.own 1) }}
    (App (Val (np @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier.ty @!!
      go!"RegisterOrUpdate")) (Val #item))
  {{ RET #(); notifierAt np (DFrac.own 1) }}

end spec
end Lease
end EtcdGrove
end Perennial
