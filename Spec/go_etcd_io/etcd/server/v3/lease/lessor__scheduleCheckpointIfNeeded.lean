/-
`(*lessor).scheduleCheckpointIfNeeded` (`server/lease/lessor.go`, names only: the trust
boundary). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.scheduleCheckpointIfNeeded(l)` (`le.mu` held): if a checkpointer is set and the lease's
remaining TTL exceeds the checkpoint interval (`int64(le.checkpointInterval.Seconds())`, a float
converted to an integer), pushes a fresh item (the lease's id, `time.Now()` plus the interval)
onto the checkpoint heap (`heap.Push`), after a debug log line. It reads `le.cp`, the lease's
`remainingTTL` and `ttl`, and the read-only configuration; the heap stays a queue of items. -/
abbrev lease.lessor.scheduleCheckpointIfNeeded.spec : Prop :=
  ∀ (lp l : Loc) (cp : GoFunc) (h : GoSlice) (hx : List (Loc × w64)) (r t : w64)
    (dq1 dq2 dq3 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorCfg lp ∗
      lF go!"cp" lp ↦{dq1} cp ∗ lF go!"leaseCheckpointHeap" lp ↦ h ∗ queueAt h hx 1 ∗
      lsF go!"remainingTTL" l ↦{dq2} r ∗ lsF go!"ttl" l ↦{dq3} t }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"scheduleCheckpointIfNeeded"))
      (Val #l))
  {{ RET #(); lF go!"cp" lp ↦{dq1} cp ∗
      (∃ (h' : GoSlice) (hx' : List (Loc × w64)), lF go!"leaseCheckpointHeap" lp ↦ h' ∗
        queueAt h' hx' 1) ∗
      lsF go!"remainingTTL" l ↦{dq2} r ∗ lsF go!"ttl" l ↦{dq3} t }}

end spec

end EtcdGrove
end Perennial
