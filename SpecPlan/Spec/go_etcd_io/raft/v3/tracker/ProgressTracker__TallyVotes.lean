/-
## `ProgressTracker.TallyVotes()`

**Users.** `raft.poll` (`raft.go:1100`: `stepCandidate` becomes leader on `VoteWon`, follower on
`VoteLost`; the counts are logged): R2's election safety (`VoteWon` only with a joint quorum of
granted votes: `jointVote`, and `Quorum.jointQ_intersect` across terms). Snippet
`raftconf/tracker.go` (`ReqTallyVotes`).

**Proof sketch.** `range p.Progress` counting the non-learners' recorded votes (`int`s below the
map's size); `JointConfig.VoteResult` over `p.Votes` (`configOwn_open`).

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__TallyVotes.lean`): the counts stated
(were unconstrained), the result as `jointVote`.

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

/-- The granted and rejected counts among the tracked voters, and the joint vote's result. -/
def ProgressTracker.TallyVotes.spec : Prop :=
  ∀ (p : Loc) (T : TrackerV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressTracker p T }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"TallyVotes")) (Val #()))
  {{ (g rj : w64), RET (PairV (PairV #g #rj) #(Quorum.jointVote T.conf.voters T.conf.votersOutgoing T.votes));
      progressTracker p T ∗
      ⌜g = W64 (tallyCount T.pv T.votes true) ∧ rj = W64 (tallyCount T.pv T.votes false)⌝ }}

end spec
end Tracker
end EtcdGrove
end Perennial
