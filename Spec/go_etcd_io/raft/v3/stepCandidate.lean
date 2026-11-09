/-
## `stepCandidate(r, m)` (internal)

**Users.** `raft.Step`'s default case at a candidate or pre-candidate.

**Proof sketch.** `MsgProp`: dropped. `MsgApp`, `MsgHeartbeat`, `MsgSnap` (of the node's term: from its leader, `msgSent_leaderOf`): `becomeFollower(term, from)` then the handler. The vote response of the node's candidacy: `poll` (the tracker records the vote: a `msgSent` response of the term, or the node's own acknowledged vote); won: a pre-candidate campaigns (`campaign(election)`: the guard `hup` checked holds while it stays a pre-candidate of the term), a candidate becomes leader (`leaderOf γ t id`: a quorum of its configuration voted for it) and broadcasts; lost: `becomeFollower(term, None)`. `MsgTimeoutNow` ignored.

**Changes** (from `specs-ref`'s `stepCandidate.lean`): over `raftCore` and the message's provenance (was
`NState`'s role and the per-type transport premises).

**Margin.** As `raft.Step`'s.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) The step of `m` at a candidate or pre-candidate of its term (after `raft.Step`'s term handling). -/
def stepCandidate.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (ml : Loc) (m : Msg) (src : StepSrc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ msgPts ml (DFrac.own 1) m ∗ stepPre r γ id m src ∗
      ⌜(ρ.role = StateCandidate ∨ ρ.role = StatePreCandidate) ∧ m.type ∉ [MsgHup, MsgVote, MsgPreVote, MsgStorageAppendResp, MsgStorageApplyResp] ∧
        (m.term = W64 0 ∨ m.term = ρ.hs.term ∨
        (m.type = MsgPreVoteResp ∧ m.reject = false ∧ uint.nat ρ.hs.term < uint.nat m.term))⌝ }}
    (App (App (Val (@! go_etcd_io.raft.v3.stepCandidate)) (Val #r)) (Val #ml))
  {{ (err : GoInterface), RET #err; ∃ ρ', raftCore r γ id ρ' ∗ stepPost γ m src ∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.type = MsgProp⌝ ∗ errIs go_etcd_io.raft.v3.ErrProposalDropped err)) }}

end spec
end Raft
end EtcdGrove
end Perennial
