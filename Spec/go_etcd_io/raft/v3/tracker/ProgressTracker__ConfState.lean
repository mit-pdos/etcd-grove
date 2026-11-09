/-
## `ProgressTracker.ConfState()`

**Users.** `switchToConfig` (`raft.go:1987`: the `ConfState` `ApplyConfChange` returns, and
`newRaft`'s/`appliedSnap`'s round-trip check `assertConfStatesEquivalent`): R2.

**Proof sketch.** `configOwn_open` for the voters; `MajorityConfig.Slice` of each of the four maps
(`sorted`, each `≤ 2^62`); `new(p.AutoLeave)`, a fresh cell, persisted (nobody writes through
it); the `ConfState` allocation, `pbRest_zero`, then `RaftPb.confStateFull_unfold` (`AutoLeave` set:
the `full` case of `confStateGo`).

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__ConfState.lean`): the lists are the
configuration's members in increasing order (was a permutation); over raftpb's `confStatePts`.
verify-round: (A5-completeness F2) returns `RaftPb.confStateFull` (was `confStatePts`, which
forgets that `AutoLeave` is set): `MemoryStorage.CreateSnapshot` and the merged snapshot message
need a full `ConfState` (`snapshotPts` is full), and Go always sets it here. Stronger post: every
caller of the old one is served (`confStateFull` gives `confStatePts` through the unfold laws,
`optCell`'s right disjunct).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api
public import Spec.go_etcd_io.raft.v3.raftpb.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- The configuration as a fresh, full `ConfState`: each list sorted, the auto-leave flag set. -/
def ProgressTracker.ConfState.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T ∗
      ⌜GMap.size T.conf.voters ≤ Quorum.sortMax ∧ GMap.size T.conf.votersOutgoing ≤ Quorum.sortMax ∧
        GMap.size T.conf.learners ≤ Quorum.sortMax ∧
        GMap.size T.conf.learnersNext ≤ Quorum.sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"ConfState")) (Val #()))
  {{ (csp : Loc), RET #csp; progressTracker p T ∗
      RaftPb.confStateFull csp (DFrac.own 1)
        ⟨Quorum.sorted T.conf.voters, Quorum.sorted T.conf.learners,
         Quorum.sorted T.conf.votersOutgoing, Quorum.sorted T.conf.learnersNext,
         T.conf.autoLeave⟩ }}

end spec
end Tracker
end EtcdGrove
end Perennial
