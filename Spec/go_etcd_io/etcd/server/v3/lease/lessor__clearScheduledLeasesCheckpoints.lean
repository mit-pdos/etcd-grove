/-
`lessor.clearScheduledLeasesCheckpoints` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart; prove-ps2-lease, 2026-11-21, for
`lessor.Demote`); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.clearScheduledLeasesCheckpoints()`: `le.leaseCheckpointHeap` set to a fresh, empty queue. -/
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
