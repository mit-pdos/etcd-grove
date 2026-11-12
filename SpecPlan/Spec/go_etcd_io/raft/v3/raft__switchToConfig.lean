/-
## `raft.switchToConfig(cfg, trk)` (internal)

**Users.** `applyConfChange` (`raft.go:1971`), `appliedSnap` (`:787`), `newRaft` (`:479`). Each
opens the tracker (`raftOpen_trk`: the tracker out, `raftTrkOpen` and the shell `trkShell` left once
its configuration and map are dropped or consumed) and gets `trkResult` from R4's `Changer` methods
(`changed B (some m')`'s `resultOk`, `Carried` giving `TrackerOk`) or `Restore` (`result`) on a
fresh tracker (`MakeProgressTracker`); `newRaft` folds the struct it built into `raftOpen` first.
**Proof sketch.** The tracker's configuration and progress replaced (R4's result for `m`: the shell
and `trkResult` fold into `progressTracker` at `m`, which `raftTrkOpen` takes); the
`ConfState` (R4's `ConfState()`: lists `m`); `isLearner` from the node's progress. A removed or
demoted leader steps down with `stepDownOnRemoval`; a leader with voters commits what the new
quorum allows (`maybeCommit`, `bcastAppend`) or probes the new peers (`maybeSendAppend`), and aborts
a transfer to a removed target: these need the closed struct, so the leader's case takes the
invariant at the new configuration (`coreInvConf`: the caller's decision moved the view to `m`).
**Changes** (from `specs-ref`'s `raft__switchToConfig.lean`): over the opened struct and R4's
result. (Integration I2: the pre is the struct with its tracker out, `raftTrkOpen` and `trkShell`,
not `raftOpen`: `applyConfChange`'s `Changer` consumes the tracker's progress map before this runs,
so `raftOpen` could not be closed in between; the post's `o'.conf = m`.) **Margin.** The view's progress pointers are not named. Verify-round (A5 completeness F2, raft-conf-pb's request): `confStateFull` (Go's `ConfState()` sets `AutoLeave`), so the server can store it in a snapshot (`CreateSnapshot`, the merged `MsgSnap`).
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

/-- (internal) Switches the tracker to `m`; returns its `ConfState`. -/
def raft.switchToConfig.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (m : Membership),
  ∀ (mi mb : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftTrkOpen r γ id o ∗
      trkShell (structFieldRef go_etcd_io.raft.v3.raft go!"trk" r) o.votes mi mb ∗ trkResult cfg trk m ∗ ⌜m.Valid⌝ ∗
      (⌜o.view.role ≠ StateLeader⌝ ∨ coreInvConf r γ id o m) }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"switchToConfig")) (Val #cfg)) (Val #trk))
  {{ (csp : Loc), RET #csp; ∃ o' cs, raftOpen r γ id o' ∗ RaftPb.confStateFull csp (DFrac.own 1) cs ∗
      ⌜o'.conf = m ∧ cs.Is m ∧ (∀ x, (o'.view.prs !! x).isSome ↔ x ∈ m.ids)⌝ ∗
      ((⌜o.view.role ≠ StateLeader ∧ o'.view.hs = o.view.hs ∧ o'.view.role = o.view.role ∧
          o'.log = o.log⌝) ∨ coreInv r γ id o') }}

end spec
end Raft
end EtcdGrove
end Perennial
