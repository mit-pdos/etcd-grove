/- Port of election_proof/spec_stepLeader.v (feb5c73d4).

## `stepLeader(r, m)` on the message types a leader handles in phase 1

`stepLeader.impl` (`Code/go_etcd_io/raft/v3.lean`; `raft.go:1262`) is *two*
type switches with a progress-map lookup in between:

    switch m.Type {                 // MsgBeat, MsgCheckQuorum, MsgProp,
    ...                             // MsgReadIndex, MsgForgetLeader
    }
    pr := r.trk.Progress[m.From]
    if pr == nil { r.logger.Debugf(...); return nil }
    switch m.Type {                 // MsgAppResp, MsgHeartbeatResp,
    ...                             // MsgSnapStatus, MsgUnreachable,
    }                               // MsgTransferLeader
    return nil

This spec covers the seven types `Step` dispatches to it.

- `MsgVoteResp`, `MsgApp`, `MsgHeartbeat`, and (since 2026-10-04) `MsgPreVoteResp` -- a
  late pre-vote response, granted at the leader's own term or a higher one -- are in
  neither switch: the progress lookup for `m.From` happens (hit or miss) and nothing
  changes. (A leader receiving `MsgApp`/`MsgHeartbeat` at its own term is excluded by
  the protocol, not by the code.)
- `MsgProp` (`raft.go:1281-1345`): `len(m.Entries) == 0` is a `Panicf` (premise `ents ≠
  []`); `r.trk.Progress[r.id] == nil` drops (dead: `id ∈ cfg`); `r.leadTransferee !=
  None` drops (dead: `HnoTransfer`); the conf-change loop reads each entry's `Type` and
  does nothing (premise: all `EntryNormal`); then `if !r.appendEntry(m.Entries...) {
  return ErrProposalDropped }` and `r.bcastAppend()`. `appendEntry` *writes*
  `Term`/`Index` into the caller's entries, so the batch is owned (not `↦*□`) and comes
  back stamped. Accepted: the log grows by the stamped batch, the self-acknowledgement
  is queued (`Step.propose`), then `bcastAppend`'s `ReplSends` (`Step.sendApps`),
  `Match` untouched. Rejected (the uncommitted-size budget, which `NState` does not
  track): the state is unchanged and `ErrProposalDropped` is returned.
- `MsgBeat`: `r.bcastHeartbeat()` (`Spec/raft__bcastHeartbeat.lean`) -- heartbeats
  `HeartbeatOk` allows, which is the model's `Step.beat`.
- `MsgHeartbeatResp`: `pr.RecentActive`, `pr.MsgAppFlowPaused` written;
  `sendAppend(m.From)` when the peer is behind or probing; then `if r.readOnly.option
  != ReadOnlySafe || len(m.Context) == 0 { return nil }`. The read-only code after it
  is skipped because a heartbeat response in scope carries no context:
  `bcastHeartbeat` sends `nil` (`heartbeatCtx`, no read requests) and `handleHeartbeat`
  echoes it -- the premise `Hctx` below. So: `ReplSends` growth, no `Match` moved (the
  model's `Step.sendApps`, or `Step.refl`).
- `MsgAppResp`, the replication path (`raft.go:1371-1565`):
  * no `Progress` for the sender: unchanged;
  * rejected: `MaybeDecrTo`, perhaps `BecomeProbe`, perhaps `sendAppend(m.From)` --
    `Next` moves, `Match` does not; `ReplSends` growth;
  * accepted: `MaybeUpdate(m.Index)` raises the sender's `Match` to `max Match m.Index`
    (the model's `Step.appResp`); then `BecomeReplicate`/`BecomeProbe`/
    `Inflights.FreeLE` as the `Progress` state says (no `Match` moves);
    `maybeCommit()` may advance `committed` to an `N` with `CommitOk` **at the updated
    `Match` map** (`Step.commit`); then `bcastAppend` (after a commit) or `sendAppend`
    (for `CanBumpCommit`) and the `for r.maybeSendAppend(m.From, false) {}` loop
    (`Step.sendApps`, judged after the commit). `releasePendingReadIndexMessages` is a
    no-op under the scope. `sendTimeoutNow` is dead: it needs `m.From =
    r.leadTransferee`, which is `0` (`ownRaftPhys`'s `HnoTransfer`), and `m.From ≠ 0`
    is a premise.

Each case is stated so that `Step` can build its `Step` witness as a chain of model
rules; `LeaderStepResult` below is that statement.

(`MsgBeat` is in `Spec/raft__handleHeartbeat.lean`, since 2026-10-02.)

Lean notes: Rocq's `app_resp_accepted`, `proposed`, `leader_propose_result`,
`leader_nonprop_result` and `leader_step_result` are `AppRespAccepted`, `proposed`,
`LeaderProposeResult`, `LeaderNonpropResult` and `LeaderStepResult` (the Prop-valued
ones UpperCamel); `if decide (P) then … else …` is `if P then … else …`; Rocq's `imap`
is `List.mapIdx`, `dom` is `domSet`, `Forall P ms` is `∀ m ∈ ms, P m`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__appendEntry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- `MsgAppResp` accepted from `src` at `index`: `s'` is `s` with the sender's `Match`
raised as `MaybeUpdate` raises it (the `Progress` values are otherwise unconstrained:
`pvs`), `committed` at `c` -- unchanged, or a `CommitOk` index judged against the
raised `Match` map -- and the outbox grown by `ms`, which `ReplSends` allows after the
commit. (Rocq's argument `from` is `src`.) -/
def AppRespAccepted (cfg : GSet w64) (id : w64) (s : NState) (src index : w64)
    (s' : NState) : Prop :=
  ∃ (x : w64) (pvs : GMap w64 Progress) (c : w64) (ms : List Msg),
    prvalsMatch s.prvals !! src = some x ∧
    prvalsMatch pvs =
      <[src := if uint.Z x < uint.Z index then index else x]> (prvalsMatch s.prvals) ∧
    (c = s.logst.committed ∨
     CommitOk cfg (toPState { s with prvals := pvs }) c) ∧
    ReplSends id { s with logst := { s.logst with committed := c } } ms ∧
    s' = { sendMsgs { s with logst := { s.logst with committed := c } } ms with
             prvals := pvs }

/-- The state `appendEntry` leaves when it accepts the batch `ents`: the log grows by
the stamped batch (`stamp`, the term and the indices after the last), and the
self-acknowledgement at the new last index is queued -- `Step.propose`'s state, under
`NStateRel`. -/
def proposed (id : w64) (s : NState) (ents : List raftpb.Entry) : NState :=
  let s1 :=
    { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }
  sendMsgs s1 [selfAck id s1]

/-- `MsgProp` at the leader: dropped and unchanged, or the batch appended and then
`bcastAppend`'s sends, judged at the appended state, with no `Match` moved. -/
def LeaderProposeResult (id : w64) (s : NState) (ents : List raftpb.Entry)
    (dropped : Bool) (s' : NState) : Prop :=
  if dropped then s' = s
  else ∃ (ms : List Msg) (pvs : GMap w64 Progress),
    s' = { sendMsgs (proposed id s ents) ms with prvals := pvs } ∧
    ReplSends id (proposed id s ents) ms ∧
    prvalsMatch pvs = prvalsMatch s.prvals

/-- What `stepLeader` does with `m`, for the types other than `MsgProp` (none of which
drops anything). The disjuncts are exclusive on `m.Type`. -/
def LeaderNonpropResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (s' : NState) : Prop :=
  ((m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
    m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp) ∧
   s' = s) ∨
  (m.Type' = MsgBeat ∧
   ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs s ms with prvals := pvs } ∧
     (∀ m' ∈ ms, HeartbeatOk id (toPState s) m') ∧
     prvalsMatch pvs = prvalsMatch s.prvals) ∨
  (m.Type' = MsgHeartbeatResp ∧
   ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs s ms with prvals := pvs } ∧
     ReplSends id s ms ∧
     prvalsMatch pvs = prvalsMatch s.prvals) ∨
  (m.Type' = MsgAppResp ∧
   ((m.From' ∉ domSet s.progress ∧ s' = s) ∨
    (m.From' ∈ domSet s.progress ∧
     m.Reject' = true ∧
     ∃ (ms : List Msg) (pvs : GMap w64 Progress),
       s' = { sendMsgs s ms with prvals := pvs } ∧
       ReplSends id s ms ∧
       prvalsMatch pvs = prvalsMatch s.prvals) ∨
    (m.From' ∈ domSet s.progress ∧
     m.Reject' = false ∧
     AppRespAccepted cfg id s m.From' m.Index' s')))

/-- What `stepLeader` does with `m`, by type. `dropped` is whether it returned
`ErrProposalDropped` (as in `FollowerStepResult`, `Spec/stepFollower.lean`); only a
`MsgProp` can be. -/
def LeaderStepResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) : Prop :=
  if m.Type' = MsgProp then
    LeaderProposeResult id s ents dropped s'
  else dropped = false ∧ LeaderNonpropResult cfg id s m s'

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Premises, each tied to the exit it rules out:
- `s.role = .leader`: `r.step = stepLeader` means it (`NStateWf`), and `toPState`'s
  `matched` is `Match` only for a leader;
- `id ∈ cfg`: `maybeCommit`'s quorum (`Spec/raft__maybeCommit.lean`);
- `m.From ≠ 0` on `MsgAppResp`: `sendTimeoutNow` is dead (`leadTransferee = 0`);
- `m.From ≠ id` where `sendAppend(m.From)` can run: `send`'s self-addressed `Panicf`.
  An accepting `MsgAppResp` may come from the node itself (`appendEntry`'s
  self-acknowledgement): the code guards every send to `m.From` by `r.id != m.From`
  there;
- `Hctx`: a `MsgHeartbeatResp` carries an empty `Context` (for any other type the wand
  is trivial);
- `MsgProp`: a non-empty batch (`Panicf` otherwise) of `EntryNormal` entries (no conf
  change in scope; the conf-change loop is then a no-op) of fewer than `2^61`
  (`appendEntry`'s no-wrap bound), and `Hents`: the batch at full ownership, since
  `appendEntry` stamps it in place. It comes back stamped in the postcondition. -/
abbrev stepLeader.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgBeat ∨
   m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨
   m.Type' = MsgProp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp) →
  s.role = .leader →
  id ∈ cfg →
  (m.Type' = MsgAppResp → m.From' ≠ W64 0) →
  (m.Type' = MsgHeartbeatResp ∨ (m.Type' = MsgAppResp ∧ m.Reject' = true) →
   m.From' ≠ id) →
  (m.Type' = MsgProp →
   ents ≠ [] ∧ (∀ e ∈ ents, e.Type' = EntryNormal) ∧
   (ents.length : Int) < 2^61 ∧
   -- the leader's term is nonzero (2026-10-10; `appendEntry`'s premise, from the
   -- ghost state: `ownRaftGhost_term_nz`)
   s.term ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hctx" ∷ (⌜m.Type' = MsgHeartbeatResp⌝ -∗
                 m.Context' ↦*□ ([] : List w8)) ∗
      "Hents" ∷ (⌜m.Type' = MsgProp⌝ -∗
                 m.Entries' ↦* ents) }}
    (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhys cfg r id s' ∗
      ⌜LeaderStepResult cfg id s m ents dropped s'⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) ∗
      (⌜m.Type' = MsgProp⌝ -∗
       m.Entries' ↦* ents.mapIdx (stamp s.term (logLast s.logst))) }}

end spec

end EtcdGrove
end Perennial
