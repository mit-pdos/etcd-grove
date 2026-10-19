/-
Port of election_proof/spec_raft__poll.v (feb5c73d4); since 2026-10-19 (witness support, raft#168)
`pollAndReportDiff`, which also returns each half's `votesToWin`.

Lean notes:
the Rocq binder `from` is `src` (`from` is a Lean keyword), as in
`recordVote`. The postcondition's `let votes' := …` is kept; its body is wrapped in
`iprop(…)` so that the separating conjunction elaborates after the `let`. The return
`(#g, #rj, #res)` is `PairV (PairV #g #rj) #res`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__VoteResultWithDifference

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `poll` records a vote and reports the tally, tied to the model's quorum conditions
by `tracker.ProgressTracker.TallyVotes.spec`.

At any configuration since 2026-10-13 (reconfiguration stage A2): the answer is exactly
`JQuorum`/`JLost` of the joint configuration (`Protocol/StepC.lean`), with no premise -- Go's
empty half wins every vote, which `MajQ` says. The statement at a simple configuration
(`cfg ≠ ∅`, `IsQuorum cfg`) was `raft.poll.specS`; it had no caller and is gone (2026-10-17). -/
abbrev raft.pollAndReportDiff.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (src : w64) (t : w32) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"pollAndReportDiff"))
      (Val #src)) (Val #t)) (Val #v))
  {{ (g rj : w64) (res : w8) (d : GoArray w64 2), RET (PairV (PairV (PairV #g #rj) #res) #d);
      let votes' := recordVote s.votes src v
      iprop(ownRaftPhysCV c c.voters r id { s with votes := votes' } ∗
      ⌜res = VoteWon ∨ res = VoteLost ∨ res = VotePending⌝ ∗
      ⌜res = VoteWon ↔ JQuorum c (granted votes')⌝ ∗
      -- see InvTracker.lean: `VoteLost` is "cannot still win", not "a majority
      -- rejected"
      ⌜res = VoteLost ↔ JLost c votes'⌝ ∗
      ⌜d.arr = [W64 (votesToWin c.incoming votes' : Int),
                W64 (votesToWin c.outgoing votes' : Int)]⌝) }}

end spec

end EtcdGrove
end Perennial
