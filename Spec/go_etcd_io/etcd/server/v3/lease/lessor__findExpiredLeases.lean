/-
`(*lessor).findExpiredLeases(limit)` (`server/lease/lessor.go:728-751`). Lean-first (no Rocq
counterpart); prove-ps2-newlessor3, 2026-11-21.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

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

/-- `le.findExpiredLeases(limit)` under the read lock (the lease map at `M`, each lease's state at
the reader's share `q`), with the notifier the field points to (the expiry loop's, out of its cell):
a fresh slice of leases of the map for which `l.expired()` returned `true` (so, if any, the
deployment premise `leasesNoExpiry` is false: `Lease.expired.spec`). -/
abbrev lease.lessor.findExpiredLeases.spec : Prop :=
  ∀ (lp lm np : Loc) (γl : GName) (dm dn : DFrac) (q : Qp) (M : GMap w64 Loc)
    (ri : _root_.Perennial.time.Duration) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"leaseMap" lp ↦{dm} lm ∗ lm ↦${dm} M ∗ lF go!"leaseExpiredNotifier" lp ↦{dn} np ∗
      notifierAt np 1 ∗ lF go!"expiredLeaseRetryInterval" lp ↦□ ri ∗
      ([∗map] _id ↦ l ∈ M, isLeaseObj γl l) ∗ ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗
      levelTok leaseLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"findExpiredLeases")) (Val #limit))
  {{ (s : GoSlice), RET #s;
      lF go!"leaseMap" lp ↦{dm} lm ∗ lm ↦${dm} M ∗ lF go!"leaseExpiredNotifier" lp ↦{dn} np ∗
      notifierAt np 1 ∗ ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗ levelTok leaseLvl ∗
      ∃ ps : List Loc, s ↦* ps ∗ ownSliceCap Loc s (DFrac.own 1) ∗
        ⌜(ps ≠ [] → ¬ leasesNoExpiry) ∧ ∀ p ∈ ps, ∃ id, M.lookup id = some p⌝ }}

end spec

end EtcdGrove
end Perennial
