/-
## `stepFollower(r, m)` (internal)

**Users.** `raft.Step`'s default case at a follower.

**Proof sketch.** `MsgProp`: dropped without a leader or with forwarding disabled; else forwarded to the leader (`send`: unstamped; its `msgSent` carries the proposals' updates as its credit). `MsgApp`, `MsgHeartbeat`, `MsgSnap`: the sender leads the term (`msgSent_leaderOf`); `handleAppendEntries`, `handleHeartbeat`, `handleSnapshot`. `MsgTransferLeader`: forwarded to the leader (stamped with the term: its `msgSent` records that the receiver led it). `MsgForgetLeader`: forget the leader (`ReadOnlySafe`: `ConfigOk`). `MsgTimeoutNow` (from the leader of the term): `hup(campaignTransfer)`. `MsgReadIndex`: forwarded to the leader, or dropped. `MsgReadIndexResp` (the leader confirmed a read: its `msgSent` carries the read's index, the update fired there): recorded as a read state (`readState`).

**Changes** (from `specs-ref`'s `stepFollower.lean`): over `raftCore` and the message's provenance (was
`NState`'s role and the per-type transport premises).

**Margin.** As `raft.Step`'s. Verify-round (A4 P3): a step from outside takes and gives back the struct's idle token (`stepPre`/`stepPost`, `coreIdle`).
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

/-- (internal) The step of `m` at a follower of its term (after `raft.Step`'s term handling). -/
def stepFollower.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (ml : Loc) (m : Msg) (src : StepSrc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ stepMsg ml m ∗ stepPre r γ id m src ∗
      ⌜ρ.role = StateFollower ∧ m.type ∉ [MsgHup, MsgVote, MsgPreVote, MsgStorageAppendResp, MsgStorageApplyResp] ∧
        (m.term = W64 0 ∨ m.term = ρ.hs.term ∨
        (m.type = MsgPreVoteResp ∧ m.reject = false ∧ uint.nat ρ.hs.term < uint.nat m.term))⌝ }}
    (App (App (Val (@! go_etcd_io.raft.v3.stepFollower)) (Val #r)) (Val #ml))
  {{ (err : GoInterface), RET #err; ∃ ρ', raftCore r γ id ρ' ∗ stepPost r γ m src ∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.type = MsgProp⌝ ∗ errIs go_etcd_io.raft.v3.ErrProposalDropped err)) }}

end spec
end Raft
end EtcdGrove
end Perennial
