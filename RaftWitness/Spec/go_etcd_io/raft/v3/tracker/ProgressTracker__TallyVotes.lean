/-
Port of election_proof/spec_ProgressTracker__TallyVotes.v (feb5c73d4).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC

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

/-- `TallyVotes` reports the outcome of the election, which is exactly the quorum
condition of the model.

The function counts the granted and rejected `t.votes` of the voters over `trk.Progress`
(a learner is skipped: `if pr.IsLearner { continue }`) and then delegates the verdict to
`p.Config.Voters.VoteResult(p.Votes)` (`JointConfig.VoteResult`, and under it
`MajorityConfig.VoteResult`), which is where the quorum arithmetic lives. The counters are
not what the postcondition talks about: the returned `g`/`rj` are existentially
quantified, since no caller reads them (`poll` returns them to `stepCandidate`, which only
looks at `res`).

**At any configuration since 2026-10-13** (reconfiguration stage A1; `ownTrackerC`): the
answer is `VoteWon` exactly when the granted votes are a quorum of both voter halves
(`JQuorum`) and `VoteLost` exactly when one half's non-rejecting voters are not a majority
of it (`JLost`) -- equivalences, with no premise: `MajQ` carries Go's convention that an
empty half wins every election. The statement at a simple configuration (`ownTracker cfg`,
`cfg ≠ ∅`, `IsQuorum cfg`) was `tracker.ProgressTracker.TallyVotes.spec_simple`; it had no caller and is gone
(2026-10-17).

History, from the Rocq port: proved 2026-09-20 after two Goose fixes (array indexing of
`quorum.JointConfig`, `len` of a nil map); the `VoteLost` conjunct was corrected 2026-09-16
from "a majority rejected" (false: 4 voters with 2 rejecting and 2 silent gives `VoteLost`
with no rejection quorum) to "cannot still win"; see `Protocol.lean`'s `Step.lose`. -/
abbrev tracker.ProgressTracker.TallyVotes.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"TallyVotes"))
      (Val #()))
  {{ (g rj : w64) (res : w8), RET (PairV (PairV #g #rj) #res);
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ JQuorum c (granted t.votes)⌝ ∗
      ⌜res = VoteLost ↔ JLost c t.votes⌝ }}

end spec

end EtcdGrove
end Perennial
