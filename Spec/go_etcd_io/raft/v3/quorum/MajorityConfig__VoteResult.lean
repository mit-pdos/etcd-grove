/-
## `MajorityConfig.VoteResult(votes)`

**Users.** `JointConfig.VoteResult` (each half). Snippet `raftconf/quorum.go` (`ReqJointVote`).

**Proof sketch.** `len(c) = 0`: `VoteWon` (`majVote ∅ _ = VoteWon`: every set is a majority of `∅`).
Else the `range` counts `votedCnt = |s ∩ granted|` and `missing = |s \ dom votes|` (`int`s below
`len(c) < 2^63`, `wp_map_len_lt`), `q = n/2 + 1`; `votedCnt ≥ q` iff `MajQ s granted`;
`votedCnt + missing = |s \ rejected|`, so `≥ q` iff `MajQ s (s \ rejected)`.

**Changes** (from `specs-ref`'s `quorum/MajorityConfig__VoteResult.lean`): the result as the model's
`majVote` (was three iff's under `s ≠ ∅`); no size premise (the map model bounds it).

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

/-- `VoteResult` of the votes over the voters `s`: `majVote s votes`. -/
def MajorityConfig.VoteResult.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (m : GoMap) (dq : DFrac) (s : GSet w64) (vm : GoMap) (dqv : DFrac)
    (votes : GMap w64 Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ p ↦{dqp} m ∗ majorityOwn m dq s ∗ ownMap vm dqv votes }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.quorum.MajorityConfig.ty @!! go!"VoteResult")) (Val #vm))
  {{ RET #(majVote s votes); p ↦{dqp} m ∗ majorityOwn m dq s ∗ ownMap vm dqv votes }}

end spec
end Quorum
end EtcdGrove
end Perennial
