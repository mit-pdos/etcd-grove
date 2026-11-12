/-
## `stepLeader(r, m)` (internal)

**Users.** `raft.Step`'s default case at a leader (`r.step`, set by `becomeLeader`).

**Proof sketch.** `MsgBeat`: `bcastHeartbeat`. `MsgCheckQuorum`: step down (`becomeFollower(term, None)`) unless a quorum was recently active; mark the others inactive. `MsgProp`: entries non-empty (`stepIn`, or the forwarder's `msgSent`); dropped (`ErrProposalDropped`, the updates dropped) when the leader is not in its configuration or transfers leadership; a conf-change entry decodes (`stepIn`, or `committedLb_confDecodes`'s source fact in `msgSent`) and is replaced by an empty normal entry (a filler: its update unfired) when one is pending or the joint transition is wrong (validation on: `ConfigOk`); `appendEntry.spec` (the updates deposited with the entries in the leader's log of its term), `bcastAppend`. `MsgReadIndex`: its update deposited at this first step (`stepIn`'s `readCtx`, or the forwarder's `msgSent`; realization item 3), postponed until an entry of the term is committed (`committedEntryInCurrentTerm.spec`'s result), else `sendMsgReadIndexResponse.spec`. With a progress for the sender: `MsgAppResp` (rejections probe back, R4's `MaybeDecrTo`; acknowledgements: R4's `MaybeUpdate`, the fork's probe shortcut only at `Next = Match + 1`, `maybeCommit` -- the quorum of the configuration in force acknowledged entries of the leader's term: they are committed, the deposited updates fire -- `releasePendingReadIndexMessages`, `bcastAppend`, more appends, the transfer's `MsgTimeoutNow`); `MsgHeartbeatResp` (an append if behind; a read acknowledgement: R3's `recvAck`/`maybeAdvance`, each read a quorum confirmed at its registered index (`readConfirmed`: its deposited update fired at every commit since, so at that index) answered by `responseToReadIndexReq.spec`: a local read state, or a response to the forwarder); `MsgSnapStatus`, `MsgUnreachable` (R4's progress); `MsgTransferLeader` (start or abort a transfer: `sendTimeoutNow` or `sendAppend`).

**Changes** (from `specs-ref`'s `stepLeader.lean`): over `raftCore` and the message's provenance (was
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

/-- (internal) The step of `m` at a leader of its term (after `raft.Step`'s term handling). -/
def stepLeader.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (ml : Loc) (m : Msg) (src : StepSrc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ stepMsg ml m ∗ stepPre r γ id m src ∗
      ⌜ρ.role = StateLeader ∧ m.type ∉ [MsgHup, MsgVote, MsgPreVote, MsgStorageAppendResp, MsgStorageApplyResp] ∧
        (m.term = W64 0 ∨ m.term = ρ.hs.term ∨
        (m.type = MsgPreVoteResp ∧ m.reject = false ∧ uint.nat ρ.hs.term < uint.nat m.term))⌝ }}
    (App (App (Val (@! go_etcd_io.raft.v3.stepLeader)) (Val #r)) (Val #ml))
  {{ (err : GoInterface), RET #err; ∃ ρ', raftCore r γ id ρ' ∗ stepPost r γ m src ∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.type = MsgProp⌝ ∗ errIs go_etcd_io.raft.v3.ErrProposalDropped err)) }}

end spec
end Raft
end EtcdGrove
end Perennial
