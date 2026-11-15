/-
## `raft.appliedSnap(snap)` (internal)

**Users.** `raft.Step`'s storage-append acknowledgement carrying the batch's snapshot (`raft.go:1197`,
`:1220`). **Proof sketch.** R3's `stableSnapTo` (`SnapAckOk`: the snapshot stored), `appliedTo` (not
a leader: a pending snapshot blocks campaigns, `promotable`), and the snapshot's configuration (the
fork's fix: only now): a new tracker (R4's `MakeProgressTracker`), `confchange.Restore` of the
`ConfState` (valid: `snapValid`'s configuration is `confAt`'s, `confAt_valid`; no panic, and
`assertConfStatesEquivalent` passes), `switchToConfig` (not a leader: no step-down, no commit).
**Changes** (from `specs-ref`'s `raft__appliedSnap.lean`): over the opened struct. **Margin.** The
progress map's new pointers are not named.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) A follower's snapshot, stored, becomes applied and its configuration the tracker's. -/
def raft.appliedSnap.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (sp : Loc) (s : Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ snapshotPts sp DFrac.discard s ∗ snapValid γ s ∗
      ⌜o.view.role ≠ StateLeader ∧ uint.nat s.index ≤ o.log.committed ∧
        o.log.SnapAckOk (uint.nat s.index)⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"appliedSnap")) (Val #sp))
  {{ RET #(); ∃ (o' : CoreOpen) (m : Membership), raftOpen r γ id o' ∗ ⌜s.conf.Is m ∧ m.Valid ∧
      o'.log.applied = max (uint.nat s.index) o.log.applied ∧
      o'.view.hs = o.view.hs ∧ o'.view.lead = o.view.lead ∧ o'.view.role = o.view.role ∧
      (∀ x, (o'.view.prs !! x).isSome ↔ x ∈ m.ids)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
