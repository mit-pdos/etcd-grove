/-
## `ProgressTracker.Committed()`

**Users.** `raft.maybeCommit` (`raft.go:796`: the leader's commit index, R2's commit safety: the
index is acknowledged by a joint quorum, `Quorum.jointIdx_quorum`). Snippet `raftconf/tracker.go`
(`ReqCommittedQuorum`).

**Proof sketch.** `configOwn_open`; the progress map as a `matchAckIndexer` interface value, whose
`isAckedIndexer` (with `P = progressMapOwn`, `acked id = (pv !! id).map matched`) is
`matchAckIndexer.AckedIndex.spec`; `JointConfig.CommittedIndex`.

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__Committed.lean`): the result as
`JointIdx` over the peers' match indices (`matchOf`).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.tracker.Api

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

/-- The largest index a joint quorum of the voters has matched. -/
def ProgressTracker.Committed.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T ∗
      ⌜GMap.size T.conf.voters ≤ Quorum.sortMax ∧ GMap.size T.conf.votersOutgoing ≤ Quorum.sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"Committed")) (Val #()))
  {{ (N : w64), RET #N; progressTracker p T ∗
      ⌜Quorum.JointIdx T.conf.voters T.conf.votersOutgoing (matchOf T.pv) N⌝ }}

end spec
end Tracker
end EtcdGrove
end Perennial
