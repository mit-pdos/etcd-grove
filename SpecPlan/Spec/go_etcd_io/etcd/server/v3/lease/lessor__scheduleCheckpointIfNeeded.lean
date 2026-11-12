/-
`(*lessor).scheduleCheckpointIfNeeded(lease)` (`lessor.go:753`): names only (an assumed internal
spec). **Users**: `Grant`, `Checkpoint`, `Promote`, on a live object, under `le.mu` (write).
**Why it is true**: `le.cp == nil`: nothing; else the object's `getRemainingTTL()` against
`int64(le.checkpointInterval.Seconds())` (a float conversion: why untranslated); above it,
`le.lg.Debug(...)` (**the logger**: `isLessor`'s `isLogger`; the zero `zap.Logger` panics here,
`specs-ref`'s axiom sweep B3-2) and `heap.Push` of a fresh cell. **Changes** (from `specs-ref`'s
`lessor__scheduleCheckpointIfNeeded.lean`, `lessorCfg` with `lg ↦□` only): `isLessor` carries
`isLogger`. **Margin**: whether a checkpoint is scheduled (time).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Internal

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

/-- **Maybe schedule a checkpoint of the live object `l`** (under the lock). -/
def lessor.scheduleCheckpointIfNeeded.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (ls : LessorState) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorFields le c (DFrac.own 1) ls ∗ ⌜∃ id e, ls.leases id = some e ∧ e.obj = l⌝ }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"scheduleCheckpointIfNeeded")) (Val #l))
  {{ RET #(); lessorFields le c (DFrac.own 1) ls }}

end spec
end Lease
end EtcdGrove
end Perennial
