/-
`tracker.ProgressTracker.QuorumActive`, Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

On the simple, learner-free tracker of `ownTracker`. The answer is whether the set `act`
of voters whose `Progress` has `RecentActive` set is a quorum of `cfg` (or `cfg` is
empty: `VoteResult` of an empty configuration is `VoteWon` by convention).

**What this does not say.** `RecentActive` is in no index: the `Progress` record
(`Defs.lean`) does not have it, and `ownProgress` hides the Goose value. So `act` is
existential -- the triple says the answer is a quorum test of *some* subset of `cfg`,
the one the flags held when read, and nothing ties it to the abstract state. Stating more
needs `RecentActive` in `Progress`. Likewise the tracker value comes back existential
(`tv'`), because `Visit`'s postcondition is existential in it. -/
abbrev tracker.ProgressTracker.QuorumActive.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"QuorumActive"))
      (Val #()))
  {{ (b : Bool) (tv' : tracker.ProgressTracker) (act : GSet w64), RET #b;
      trk ↦ tv' ∗ ownTracker cfg tv' t ∗ ⌜act ⊆ cfg⌝ ∗
      ⌜b = true ↔ (cfg = ∅ ∨ IsQuorum cfg act)⌝ }}

end spec

end EtcdGrove
end Perennial
