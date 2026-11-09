/-
`(*lessor).initAndRecover()` (`lessor.go:808`), an internal helper's spec (mirrors the code).
**Users**: `newLessor`, `Recover`, under `le.mu` (or before the lessor is shared), with fresh maps.
**Proof sketch**: `le.b.BatchTx()`, `LockOutsideApply` (`beOk`), 4b's `UnsafeCreateLeaseBucket`
(no change: the bucket exists or is created empty) and `MustUnsafeGetAllLeases`
(`Schema.MustUnsafeGetAllLeases.spec` over `Schema.txRd` and the view of `beLeases ls.be ls.bkt`:
one fresh `leaseAt p r` per record, each id once, in some order; the map assignments below do not
depend on the order), `Unlock`; a fresh object per record, its TTL raised to
`minLeaseTTL`; the notifier's `Init`, `heap.Init` of the checkpoint heap; `ForceCommit()`.
**Changes** (from `specs-ref`'s `lessor__initAndRecover.lean`, the tracked buckets): over
`lessorFields` and 4b's `beLeases` (inside it). **Margin**: none.
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

/-- **Load the leases of the backend's bucket** into empty maps (under the lock). -/
def lessor.initAndRecover.spec : Prop :=
  ∀ (le : Loc) (c : Cfg) (ls : LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ beOk ls.be ∗
      lessorFields le c (DFrac.own 1)
        { ls with leases := fun _ => none, items := fun _ => 0 } }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"initAndRecover")) (Val #()))
  {{ RET #(); beOk ls.be ∗ ∃ objs : Int → Loc,
      lessorFields le c (DFrac.own 1) (LessorState.loaded c ls.be ls.rd ls.bkt objs ls.keys) }}

end spec
end Lease
end EtcdGrove
end Perennial
