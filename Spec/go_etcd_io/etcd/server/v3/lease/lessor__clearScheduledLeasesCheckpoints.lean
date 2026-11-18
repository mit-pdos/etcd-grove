/-
`(*lessor).clearScheduledLeasesCheckpoints()` (`server/lease/lessor.go`). Lean-first (no Rocq
counterpart); translated with its body for `Demote` (the lessor-noax stage, 2026-11-18).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.clearScheduledLeasesCheckpoints()` (the heap's field owned, under the write lock): the
field set to an empty queue. -/
abbrev lease.lessor.clearScheduledLeasesCheckpoints.spec : Prop :=
  ∀ (lp : Loc) (h : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"leaseCheckpointHeap" lp ↦ h }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"clearScheduledLeasesCheckpoints"))
      (Val #()))
  {{ RET #(); ∃ h' : GoSlice, lF go!"leaseCheckpointHeap" lp ↦ h' ∗ queueAt h' [] 1 }}

end spec

end EtcdGrove
end Perennial
