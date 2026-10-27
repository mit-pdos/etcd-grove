/-
New in etcd-io/raft#168 (share witness), Lean-first (`notes/pr-verify/raft-168.md`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC
public import RaftWitness.Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResultWithDifference

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `TallyVotesWithDifference` (raft#168, tracker.go): `TallyVotes` with
`JointConfig.VoteResultWithDifference` in place of `JointConfig.VoteResult`, also returning each
voter half's `votesToWin` (`stepCandidate` asks a witness for its vote when one of them is
`1`). The verdict is `TallyVotes`'s, conjunct for conjunct, at any configuration
(`ownTrackerC`): the PR does not change how an election is decided. -/
abbrev tracker.ProgressTracker.TallyVotesWithDifference.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"TallyVotesWithDifference")) (Val #()))
  {{ (g rj : w64) (res : w8) (d : GoArray w64 2), RET (PairV (PairV (PairV #g #rj) #res) #d);
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ JQuorum c (granted t.votes)⌝ ∗
      ⌜res = VoteLost ↔ JLost c t.votes⌝ ∗
      ⌜d.arr = [W64 (votesToWin c.incoming t.votes : Int),
                W64 (votesToWin c.outgoing t.votes : Int)]⌝ }}

end spec

end EtcdGrove
end Perennial
