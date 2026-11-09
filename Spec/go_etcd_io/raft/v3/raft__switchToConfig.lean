/-
## `raft.switchToConfig(cfg, trk)` (internal)

**Users.** `applyConfChange` (`raft.go:1971`), `appliedSnap` (`:787`), `newRaft` (`:479`).
**Proof sketch.** The tracker's configuration and progress replaced (R4's result for `m`); the
`ConfState` (R4's `ConfState()`: lists `m`); `isLearner` from the node's progress. A removed or
demoted leader steps down with `stepDownOnRemoval`; a leader with voters commits what the new
quorum allows (`maybeCommit`, `bcastAppend`) or probes the new peers (`maybeSendAppend`), and aborts
a transfer to a removed target: these need the closed struct, so the leader's case takes the
invariant at the new configuration (`coreInvConf`: the caller's decision moved the view to `m`).
**Changes** (from `specs-ref`'s `raft__switchToConfig.lean`): over the opened struct and R4's
result. **Margin.** The view's progress pointers are not named.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) Switches the tracker to `m`; returns its `ConfState`. -/
def raft.switchToConfig.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (m : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ trkResult cfg trk m ∗ ⌜m.Valid⌝ ∗
      (⌜o.view.role ≠ StateLeader⌝ ∨ coreInvConf r γ id o m) }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"switchToConfig")) (Val #cfg)) (Val #trk))
  {{ (csp : Loc), RET #csp; ∃ o' cs, raftOpen r γ id o' ∗ confStatePts csp (DFrac.own 1) cs ∗
      ⌜cs.Is m ∧ (∀ x, (o'.view.prs !! x).isSome ↔ x ∈ m.ids)⌝ ∗
      ((⌜o.view.role ≠ StateLeader ∧ o'.view.hs = o.view.hs ∧ o'.view.role = o.view.role ∧
          o'.log = o.log⌝) ∨ coreInv r γ id o') }}

end spec
end Raft
end EtcdGrove
end Perennial
