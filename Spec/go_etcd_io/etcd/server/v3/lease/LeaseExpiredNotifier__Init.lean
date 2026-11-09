/-
`(*LeaseExpiredNotifier).Init()` (`lease_queue.go:75`), an internal helper's spec (mirrors the
code). **Users**: `initAndRecover`. **Proof sketch**: `heap.Init` of the queue (4b's `container/heap`
boundary: a permutation, indices kept by `Swap`), a fresh map rebuilt from the queue's cells.
**Changes** (from `specs-ref`'s `LeaseExpiredNotifier__Init.lean`): unchanged in substance.
**Margin**: none.
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

/-- **Rebuild the notifier's heap and map.** -/
def LeaseExpiredNotifier.Init.spec : Prop :=
  ∀ (np : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ notifierQ np }}
    (App (Val (np @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier.ty @!!
      go!"Init")) (Val #()))
  {{ RET #(); notifierAt np (DFrac.own 1) }}

end spec
end Lease
end EtcdGrove
end Perennial
