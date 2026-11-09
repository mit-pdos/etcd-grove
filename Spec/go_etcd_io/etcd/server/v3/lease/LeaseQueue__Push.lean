/-
`(*LeaseQueue).Push(x)` (`lease_queue.go:45`), an internal helper's spec (mirrors the code).
**Users**: `heap.Push` (the notifier's `RegisterOrUpdate`, `scheduleCheckpointIfNeeded`). **Proof
sketch**: `x.(*LeaseWithTime)` (the argument is one: no panic), its index set to the length,
appended. **Changes** (from `specs-ref`'s `LeaseQueue__Push.lean`): unchanged. **Margin**: none.
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

/-- **Append a cell** to the queue `qf` points to. -/
def LeaseQueue.Push.spec : Prop :=
  ∀ (qf : Loc) (s : GoSlice) (xs : List (Loc × w64)) (p : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ qf ↦ s ∗
      queueAt s xs (DFrac.own 1) ∗ lwtAt p id (DFrac.own 1) }}
    (App (Val (qf @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.LeaseQueue.ty @!!
      go!"Push"))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.LeaseWithTime.ty)
        #p : GoInterface)))
  {{ RET #(); ∃ s' : GoSlice, qf ↦ s' ∗ queueAt s' (xs ++ [(p, id)]) (DFrac.own 1) }}

end spec
end Lease
end EtcdGrove
end Perennial
