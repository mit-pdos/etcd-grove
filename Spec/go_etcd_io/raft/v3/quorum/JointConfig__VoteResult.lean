/-
## `JointConfig.VoteResult(votes)`

**Users.** `ProgressTracker.TallyVotes` (`tracker.go:252`: `raft.poll`, the election, R2),
`ProgressTracker.QuorumActive` (`tracker.go:192`: CheckQuorum). Snippet `raftconf/quorum.go`
(`ReqJointVote`, `ReqEmptyHalf`).

**Proof sketch.** Each half's `VoteResult`, combined as Go does (`jointVote`).

**Changes** (from `specs-ref`'s `quorum/JointConfig__VoteResult.lean`): the result as the model's
`jointVote` (was the won/lost iff's, which follow from its definition); no size premise.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Quorum

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.quorum.Assumptions]

/-- The joint vote's result: `jointVote s0 s1 votes` (won iff both halves won). -/
def JointConfig.VoteResult.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (c : go_etcd_io.raft.v3.quorum.JointConfig) (dq : DFrac)
    (s0 s1 : GSet w64) (vm : GoMap) (dqv : DFrac) (votes : GMap w64 Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ p ↦{dqp} c ∗ jointConfigOwn c dq s0 s1 ∗ ownMap vm dqv votes }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.quorum.JointConfig.ty @!! go!"VoteResult")) (Val #vm))
  {{ RET #(jointVote s0 s1 votes); p ↦{dqp} c ∗ jointConfigOwn c dq s0 s1 ∗
      ownMap vm dqv votes }}

end spec
end Quorum
end EtcdGrove
end Perennial
