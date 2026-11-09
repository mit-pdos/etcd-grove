/-
## `raft.Step(m)`

**Users** (every caller is in the raft package; no client sees the raft struct):
- `node.run` (`node.go:384`, `:392`): proposals from `propc` (`From` set to the node's id, the
  client's update riding with them: R1's `node.Propose`/`ProposeConfChange`), and `recvc`: received
  messages (`node.Step`: `msgSent`, credit, address), local reads (`node.ReadIndex`: the registered
  context) and reports (`Campaign`, `ReportUnreachable`, `ReportSnapshot`, `TransferLeadership`,
  `ForgetLeader`);
- `RawNode`'s `Campaign`, `Propose`, `ProposeConfChange`, `Step`, `ReportUnreachable`,
  `ReportSnapshot`, `TransferLeader`, `ForgetLeader`, `ReadIndex` (`rawnode.go:85`-`:521`), and
  `Advance` (`rawnode.go:451`: the acknowledgements `acceptReady` queued: `StepSrc.ack`);
- raft.go itself: `tickElection` (`MsgHup`), `tickHeartbeat` (`MsgCheckQuorum`, `MsgBeat`),
  `appliedTo` (the auto-leave proposal: an empty `EntryConfChangeV2`, raft's own).
Snippets: `step.go` (every source; the only error), `ready.go` (`ReqAdvanceAcks`).

**Proof sketch.** `traceReceiveMessage` (a no-op). **The term.** A local message (term 0) goes on. A
higher term: a vote request inside a leader's lease with `checkQuorum` is ignored; else (but for a
pre-vote, or a granted pre-vote response) `becomeFollower(m.term, lead)`, `lead` the sender for an
append, heartbeat or snapshot (`msgSent_leaderOf`: it led that term), none otherwise; the new term
is volatile (persisted with the next batch). A lower term: a `checkQuorum`/`preVote` node answers a
stale append or heartbeat with an empty `MsgAppResp` of its term, a stale pre-vote with a rejection,
applies a stale storage acknowledgement's snapshot (committed state, term-independent), and ignores
the rest. **The handlers.** `MsgHup`: `hup` (its own checks: not leader, promotable, no unapplied
conf entry, no pending snapshot: the campaign guard the cluster invariant needs for the candidate's
quorum to be of the configuration in force; the term's increase takes a receipt). `MsgVote`/
`MsgPreVote`: the vote rule (a repeat, or no vote and no leader, or a future pre-vote; and the
candidate's log at least as up to date: R3's `isUpToDate`); a granted vote is recorded in `Vote`
and its response queued after the append (`msgsAfterAppend`): its `msgSent` (the vote's protocol
fact) is minted only when the batch carrying the vote is entered, at the durable vote. The storage
acknowledgements (`StepSrc.ack`, R1's `Advance`): `stableTo` the batch's last entry (the storage
holds it: `readyStor ... none k []`), `appliedSnap` (the snapshot's configuration, R4's `Restore`
of a valid configuration: `snapValid`; the view moves to it, `ackPost`), `appliedTo` the delivered
log (its conf entries applied or decided skip: `confSkipped`; at a joint leader with auto-leave the
leave entry is proposed, raft's own) and `reduceUncommittedSize`. The rest: `r.step`, the role's
handler (`stepLeader.spec`, `stepCandidate.spec`, `stepFollower.spec`), whose only error is a
dropped proposal.

**Changes** (from `specs-ref`'s `raft__Step.lean`, revised 48 times by scope extensions): one
precondition, the message's provenance (`stepIn`, or an acknowledgement), for every type and
feature; nothing of the node's state but the view `ρ` is in the statement (was `NState` with
`LocalFrame`, `NetFrame`, `TermStep`, `RespStep`, `SnapStep`, `PreCandStep`, `RestMsgOk`'s
transport premises: a stamped `MsgTransferLeader`'s receiver, a `MsgTimeoutNow`'s term budget). The
facts those frames carried for the `RawNode` layer are its phases (`rawNodeAt`, `readyKept`:
`ApiCore.lean`), the term budget is the cluster's (receipts), and a stamped transfer request's
receiver is a fact of its `msgSent`.

**Margin.** Says nothing of the new view `ρ'` (the getters read it); a proposal dropped may still be
forwarded and commit (R1's `propErr`); `ErrProposalDropped` is returned only for `MsgProp`.
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

/-- **Steps message `m`** at node `id`'s raft struct, from any source: the struct stays raft's; the error is `nil`, or `ErrProposalDropped` for a proposal. -/
def raft.Step.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (ml : Loc) (m : Msg) (src : StepSrc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ msgPts ml (DFrac.own 1) m ∗ stepPre r γ id m src }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface), RET #err; ∃ ρ', raftCore r γ id ρ' ∗ stepPost γ m src ∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.type = MsgProp⌝ ∗ errIs go_etcd_io.raft.v3.ErrProposalDropped err)) }}

end spec
end Raft
end EtcdGrove
end Perennial
