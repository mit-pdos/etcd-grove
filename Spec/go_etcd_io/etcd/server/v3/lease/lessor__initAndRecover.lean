/-
`(*lease.lessor).initAndRecover()` (`lessor.go:808`). Lean-first (no Rocq counterpart); the
lease-expiry plan's S1 (2026-11-04), for `Recover`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorRecover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`le.initAndRecover()`** under `le.mu` (its caller, `Recover`, holds the lock and the fields):
the lessor's `b` the real backend at `be`, its lease map `lm` empty, its minimum TTL `mt`, its
expiry notifier and checkpoint heap; the backend open, two write-back tokens and a part of the
tracked buckets `S` containing `lease`, whose `lease` bucket holds the records of `recs`, in key
order (`bktEnts`, `leaseRecEnc`: what `Grant` writes). `b.BatchTx()`, `LockOutsideApply`,
`UnsafeCreateLeaseBucket` (present or created empty), `MustUnsafeGetAllLeases` (the records),
`Unlock` (one token; the part idle after it), then one lease per record into the map, each with its
TTL raised to `mt` (`recLease`), the notifier and the heap re-initialized, `ForceCommit` (one
token). The map holds the recovered leases (`recMap`), one per record, with a time receipt of their
number. -/
abbrev lease.lessor.initAndRecover.spec : Prop :=
  ∀ (lp lm np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (mt : w64) (γB : backend.BNames)
    (P : backend.BParams) (W Pk : IProp GF) (be : Loc) (qo : Qp) (S : GoString → Prop)
    (r : GMap GoString backend.BktData) (recs : List (w64 × w64 × w64)),
  S mvcc.leaseName → mvcc.leaseParams P →
  backend.bktEnts ((r.lookup mvcc.leaseName).getD ∅) = recs.map leaseRecEnc →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"b" lp ↦ (interface.mkOk (go.GoType.PointerType backend.backend.ty) #be : GoInterface) ∗
      lF go!"leaseMap" lp ↦ lm ∗ lm ↦$ (∅ : GMap w64 Loc) ∗ lF go!"minLeaseTTL" lp ↦□ mt ∗
      lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt np 1 ∗
      lF go!"leaseCheckpointHeap" lp ↦ h ∗ queueAt h hx 1 ∗
      backend.isBackend γB P W Pk be ∗ backend.bOpen γB qo ∗ ownToks γB.wb 2 ∗
      backend.rbPart γB S r }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"initAndRecover")) (Val #()))
  {{ RET #(); ∃ (ls : List Loc) (h' : GoSlice) (hx' : List (Loc × w64)),
      ⌜ls.length = recs.length⌝ ∗
      lF go!"b" lp ↦ (interface.mkOk (go.GoType.PointerType backend.backend.ty) #be : GoInterface) ∗
      lF go!"leaseMap" lp ↦ lm ∗ lm ↦$ recMap (recs.zip ls) ∗
      ([∗list] p ∈ recs.zip ls, recLease mt p.1 p.2) ∗ ⧖ recs.length ∗
      lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt np 1 ∗
      lF go!"leaseCheckpointHeap" lp ↦ h' ∗ queueAt h' hx' 1 ∗
      backend.bOpen γB qo ∗
      backend.rbOwnIn γB S (r.insert mvcc.leaseName ((r.lookup mvcc.leaseName).getD ∅)) }}

end spec

end EtcdGrove
end Perennial
