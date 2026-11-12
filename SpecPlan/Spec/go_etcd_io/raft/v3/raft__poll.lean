/-
## `raft.poll(id, t, v)` (internal)

**Users.** `stepCandidate` (`raft.go:1712`). **Proof sketch.** R4's `RecordVote` (the first vote of a
voter counts) and `TallyVotes` (the joint quorum of the configuration in force). The votes recorded
are each a `voteFrom` of the node's term (a `msgSent` vote response, `msgSent_voteFrom`, or the
node's own durable vote, acknowledged at `Advance`); `VoteWon` at a candidate is a quorum of granted
votes: `leaderOf γ term id` (election safety: each voter's durable vote is one per term).
**Changes** (from `specs-ref`'s `raft__poll.lean`): over `voteFrom` (was the message's record).
**Margin.** The counts are not stated.
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

/-- (internal) Records a vote and tallies; a won election makes the node its term's leader. -/
def raft.poll.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (src : w64) (t : w32) (v : Bool) (T : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗
      ⌜(o.view.role = StateCandidate ∨ o.view.role = StatePreCandidate) ∧
        (T = o.view.hs.term ∨ (t = MsgPreVoteResp ∧ T = o.view.hs.term + W64 1))⌝ ∗
      voteFrom γ id T t src v }}
    (App (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"poll")) (Val #src)) (Val #t)) (Val #v))
  {{ (gr rj : w64) (res : w8), RET (PairV (PairV #gr #rj) #res); ∃ o', raftOpen r γ id o' ∗
      coreInv r γ id o' ∗ ⌜o'.view = o.view ∧ o'.log = o.log⌝ ∗
      (⌜res = voteWon ∧ o.view.role = StateCandidate ∧ t = MsgVoteResp⌝ -∗
        leaderOf γ o.view.hs.term id) }}

end spec
end Raft
end EtcdGrove
end Perennial
