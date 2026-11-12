/-
`tracker.ProgressTracker.QuorumActive`, Lean-first (no Rocq counterpart).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTracker

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

/-- `p.QuorumActive()` (`tracker.ProgressTracker.QuorumActive.impl`,
`Code/go_etcd_io/raft/v3/tracker.lean`; tracker.go:208):

    votes := map[uint64]bool{}
    p.Visit(func(id uint64, pr *Progress) {
      if pr.IsLearner { return }
      votes[id] = pr.RecentActive
    })
    return p.Voters.VoteResult(votes) == quorum.VoteWon

At any configuration since 2026-10-13 (reconfiguration stage A1; `ownTrackerC`): the answer is
whether the set `act` of voters whose `Progress` has `RecentActive` set is a quorum of both
voter halves (`JQuorum`; an empty half is no constraint). The statement at a simple
configuration (`ownTracker cfg`: `cfg = ∅ ∨ IsQuorum cfg act`) was
`tracker.ProgressTracker.QuorumActive.spec_simple`; it had no caller and is gone (2026-10-17).

**What this does not say.** `RecentActive` is in no index: the `Progress` record
(`Defs.lean`) does not have it, and `ownProgress` hides the Goose value. So `act` is
existential -- the triple says the answer is a quorum test of *some* set of voters, the one
the flags held when read, and nothing ties it to the abstract state. Stating more needs
`RecentActive` in `Progress`. Likewise the tracker value comes back existential (`tv'`),
because `Visit`'s postcondition is existential in it. -/
abbrev tracker.ProgressTracker.QuorumActive.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"QuorumActive"))
      (Val #()))
  {{ (b : Bool) (tv' : tracker.ProgressTracker) (act : GSet w64), RET #b;
      trk ↦ tv' ∗ ownTrackerC c tv' t ∗ ⌜act ⊆ c.voters⌝ ∗
      ⌜b = true ↔ JQuorum c act⌝ }}

end spec

end EtcdGrove
end Perennial
