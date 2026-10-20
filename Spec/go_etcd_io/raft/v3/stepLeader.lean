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

This spec covers the types `Step` dispatches to it.

- `MsgCheckQuorum` (2026-10-17, `CheckQuorum` on): `QuorumActive()` (the voters whose
  `Progress.RecentActive` is set, a joint quorum or not); if not, `becomeFollower(r.Term,
  None)` -- the model's `Step.stepDown`; then `Visit` clears every other peer's
  `RecentActive`, which no `Progress` record holds.

- `MsgVoteResp`, `MsgApp`, `MsgHeartbeat`, and (since 2026-10-04) `MsgPreVoteResp` -- a
  late pre-vote response, granted at the leader's own term or a higher one -- are in
  neither switch: the progress lookup for `m.From` happens (hit or miss) and nothing
  changes. (A leader receiving `MsgApp`/`MsgHeartbeat` at its own term is excluded by
  the protocol, not by the code.)
- `MsgProp` (`raft.go:1281-1345`): `len(m.Entries) == 0` is a `Panicf` (premise `ents ≠
  []`); `r.trk.Progress[r.id] == nil` drops (dead: `id ∈ cfg`); `r.leadTransferee !=
  None` drops (a leader transfer in progress); the conf-change loop (since 2026-10-13,
  reconfiguration stage D; until then a premise made every entry `EntryNormal` and the loop
  a no-op) decodes each conf-change entry (`Unmarshal`, which must not fail: `"Hcc"`,
  `ccEntsOk`, gives the bytes and what they decode to) and refuses it -- writing
  `pb.Entry{Type: EntryNormal}` over it in the caller's batch -- when a conf change is
  pending (`pendingConfIndex > applied`) or it is an empty `ConfChangeV2` (a request to
  leave a joint configuration, which the configuration in use never is: `alreadyJoint` is
  `false`), and otherwise accepts it and moves `pendingConfIndex` to its index-to-be
  (`propConf`, `CCModel.lean`; `Config.DisableConfChangeValidation` is `false`, `newRaft`'s
  premise); then `if !r.appendEntry(m.Entries...) { return ErrProposalDropped }` and
  `r.bcastAppend()`. `appendEntry` *writes* `Term`/`Index` into the caller's entries, so
  the batch is owned (not `↦*□`). Accepted: the log grows by the loop's batch, stamped, the
  self-acknowledgement is queued (`Step.propose`), then `bcastAppend`'s `ReplSends`
  (`Step.sendApps`), `Match` untouched. Rejected (the uncommitted-size budget, which
  `NState` does not track): only `pendingConfIndex` has moved, and `ErrProposalDropped` is
  returned.
- `MsgBeat`: `r.bcastHeartbeat()` (`Spec/raft__bcastHeartbeat.lean`) -- heartbeats
  `HeartbeatOk` allows, which is the model's `Step.beat`.
- `MsgHeartbeatResp`: `pr.RecentActive`, `pr.MsgAppFlowPaused` written;
  `sendAppend(m.From)` when the peer is behind or probing; then `if r.readOnly.option
  != ReadOnlySafe || len(m.Context) == 0 { return nil }`: `ReplSends` growth, no
  `Match` moved (the model's `Step.sendApps`, or `Step.refl`). (2026-10-12) With a
  context (`m.Context ↦*□ ctx`, `Hctx`; the option is always `ReadOnlySafe`):
  `recvAck(m.From, m.Context)`, `maybeAdvance(r.trk.Voters)`, and each confirmed request
  answered (`ReadAckResult`). A sender with no `Progress` returns before all this, so
  its context is ignored (the `m.From ∉ domSet s.progress` disjunct, 2026-10-13).
- `MsgReadIndex` (2026-10-12): pending until an entry of the leader's term is committed
  (`committedEntryInCurrentTerm`), then `sendMsgReadIndexResponse` (since 2026-10-14, the
  pinned raft having the single-voter fix, also at a single voter: there the shortcut is in
  `sendMsgReadIndexResponse`; until then it was a premise).
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
    (`Step.sendApps`, judged after the commit). After a commit,
    `releasePendingReadIndexMessages` releases the pending read-index requests
    (2026-10-12), its heartbeats judged at the raised `Match` map. `sendTimeoutNow` is dead: it needs `m.From =
    r.leadTransferee`, which is `0` (`ownRaftPhys`'s `HnoTransfer`), and `m.From ≠ 0`
    is a premise.

Each case is stated so that `Step` can build its `Step` witness as a chain of model
rules; `LeaderStepResultC` below is that statement.

(`MsgBeat` is in `Spec/raft__handleHeartbeat.lean`, since 2026-10-02.)

Lean notes: Rocq's `app_resp_accepted`, `proposed`, `leader_propose_result`,
`leader_nonprop_result` and `leader_step_result` are `AppRespAccepted`, `proposed`,
`LeaderProposeResult`, `LeaderNonpropResult` and `LeaderStepResult` (the Prop-valued
ones UpperCamel); `if decide (P) then … else …` is `if P then … else …`; Rocq's `imap`
is `List.mapIdx`, `dom` is `domSet`, `Forall P ms` is `∀ m ∈ ms, P m`.

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`), taken as `Step` passes it
(`msgIn ml dqe`: the struct and its `Entries` capacity owned, the entry pointers at `1` for a
`MsgProp` -- the conf-change loop replaces a refused entry's slot with a fresh `&pb.Entry{Type:
EntryNormal}` -- and read-only otherwise) and not given back: a `MsgReadIndex` is frozen and kept
(the pending slice, the read-only queue), the rest is dropped. `appendEntry` no longer writes the
batch but appends stamped clones, which hold the same records (D6: an entry's `Data'` is its
bytes; `Spec/raft__appendEntry.lean`), so `LeaderProposeResult` is the old one; the post's
`(⌜MsgProp⌝ -∗ ∃ ents', m.Entries' ↦* ents')` is gone. (Phase 2 of R4 had the log grow by
copies `ents'` whose `Data` slices were fresh, `EntsDataCopy`, and the data bytes a premise
`"Hdata"`; D6 removed both.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Proof.go_etcd_io.raft.v3.WAppSentStep
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raft__maybeStartNewSubterm
-- read-index (2026-10-12)
public import Spec.go_etcd_io.raft.v3.releasePendingReadIndexMessages
public import Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `releasePendingReadIndexMessages`' heartbeats at `s` (2026-10-12): `HeartbeatOk`, each
with the position after one of the released requests. -/
def ReleaseHbs (id : w64) (s : NState) (hb : List Msg) : Prop :=
  ∀ m' ∈ hb, HeartbeatOk id (toPState s) m' ∧
    ∃ k, 0 < k ∧ k ≤ s.rd.pend.length ∧
      m'.ctx = hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k))

/-- The state `appendEntry` leaves when it accepts the batch `ents`: the log grows by
the stamped batch (`stampS`, the term, the node's subterm and the indices after the last), and the
self-acknowledgement at the new last index is queued -- `Step.propose`'s state, under
`NStateRel`. -/
def proposed (id : w64) (s : NState) (ents : List EntryM) : NState :=
  let s1 :=
    { s with logst := logAppend s.logst (ents.mapIdx (stampS s.term s.ep.sub (logLast s.logst))) }
  sendMsgs s1 [selfAck id s1]

/-- `stepLeader`'s conf-change loop at `s` (2026-10-13): the batch it leaves and
`pendingConfIndex` (`propConf`, `CCModel.lean`), for the decoded conf changes `cs`; `joint`
(2026-10-14, reconfiguration stage A3) is whether the configuration in use is joint. -/
def leaderPropConf (s : NState) (ents : List EntryM) (cs : List (Option CCMsg))
    (joint : Bool := false) : List EntryM × w64 :=
  propConf s.logst.applied (logLast s.logst) s.pci ents cs joint

/-- `MsgProp` at the leader: dropped -- unchanged (a leader transfer in progress, before
the conf-change loop), or with only `pendingConfIndex` moved by the loop (`appendEntry`
refused the batch) -- or the loop's batch appended and then `bcastAppend`'s sends, judged
at the appended state, with no `Match` moved; for some decoded conf changes `cs` of the
batch (2026-10-13; until then the batch was appended as proposed). `joint` (2026-10-14,
reconfiguration stage A3): whether the configuration in use is joint, which decides which conf
changes the loop refuses (`propConf`); `false` at a simple configuration. (2026-10-15, stage
R4) What is appended is `appendEntry`'s clones of the loop's batch, which hold the same records
(D6). -/
def LeaderProposeResult (id : w64) (s : NState) (ents : List EntryM)
    (dropped : Bool) (s' : NState) (joint : Bool := false) : Prop :=
  ∃ cs : List (Option CCMsg), CCTypesOk ents cs ∧
  if dropped then s' = s ∨ s' = { s with pci := (leaderPropConf s ents cs joint).2 }
  else ∃ (ms : List Msg) (pvs : GMap w64 Progress),
    s' = { sendMsgs (proposed id { s with pci := (leaderPropConf s ents cs joint).2 }
             (leaderPropConf s ents cs joint).1) ms with prvals := pvs } ∧
    ReplSends id (proposed id { s with pci := (leaderPropConf s ents cs joint).2 }
      (leaderPropConf s ents cs joint).1) ms ∧
    prvalsMatch pvs = prvalsMatch s.prvals

/-- What the read-index code needs of the read-only state (2026-10-12; the ghost state,
`ownReadGhost`, keeps it): every voter's acknowledgement is a position sent (at most the
queue's end, so `maybeAdvance` does not panic), and every request has entries (its
context is the first's data). -/
def RdOk (cfg : GSet w64) (rd : RdState) : Prop :=
  (∀ v ∈ cfg, uint.Z ((rd.ro.acks !! v).getD (W64 0))
                ≤ uint.Z rd.ro.confirmed + (rd.ro.pending.length : Int)) ∧
  (∀ q ∈ rd.ro.pending, q.ents ≠ []) ∧
  (∀ p ∈ rd.pend, p.2 ≠ [])

/-! ### At any configuration (2026-10-14, reconfiguration stage A3) -/

-- `CfgM.joint` (`alreadyJoint`) is in `Protocol/StepC.lean` since stage B3.

/-- `MsgAppResp` accepted from `src` at `index`: `s'` is `s` with the sender's `Match`
raised as `MaybeUpdate` raises it (the `Progress` values are otherwise unconstrained:
`pvs`), `committed` at `n` -- unchanged, or a `CommitOkC` index (a joint quorum) judged
against the raised `Match` map -- and the outbox grown by `ms`, which `ReplSends` allows after
the commit. A commit releases the pending read-index requests (2026-10-12), with their
heartbeats `hb` judged at the raised `Match` map (2026-10-13: a heartbeat's `Commit` is
`min(Match, committed)` of the `Progress` it is sent from) -- or (2026-10-14, the single-voter
fix) at a configuration whose only voter is the leader itself, each answered at once at the new
commit index. (Until 2026-10-14 also `AppRespAccepted`, at a simple configuration.) -/
def AppRespAcceptedC (c : CfgM) (id : w64) (s : NState) (src index : w64)
    (s' : NState) : Prop :=
  ∃ (x : w64) (pvs : GMap w64 Progress) (n : w64) (hb ms ws : List Msg),
    prvalsMatch s.prvals !! src = some x ∧
    prvalsMatch pvs =
      <[src := if uint.Z x < uint.Z index then index else x]> (prvalsMatch s.prvals) ∧
    (n = s.logst.committed ∨
     CommitOkC c (toPState { s with prvals := pvs }) n) ∧
    -- (2026-10-20, witness support) `maybeCommit`'s requests to the witness (`SendWAppOk`)
    (∀ m ∈ ws, SendWAppOk c id (toPState { s with prvals := pvs }) m) ∧
    ReplSends id { sendMsgs s ws with logst := { s.logst with committed := n } } ms ∧
    (if n = s.logst.committed then hb = [] ∧
       s' = { sendMsgs { sendMsgs s ws with logst := { s.logst with committed := n } } ms with
                prvals := pvs }
     else (¬ CfgSingle c id ∧
        ReleaseHbs id { sendMsgs s ws with logst := { s.logst with committed := n }, prvals := pvs } hb ∧
        s' = { sendMsgs (sendMsgs (releasedState id
                 { sendMsgs s ws with logst := { s.logst with committed := n } }) hb) ms with
                 prvals := pvs }) ∨
       (CfgSingle c id ∧ hb = [] ∧
        s' = { sendMsgs (readRespondAll id
                 { sendMsgs s ws with logst := { s.logst with committed := n }, rd := { s.rd with pend := [] } }
                 (pendReqs { sendMsgs s ws with logst := { s.logst with committed := n } })) ms with
                 prvals := pvs }))

/-- The read path of a `MsgHeartbeatResp` with a context (2026-10-12): the sender's
acknowledgement, the requests up to the joint quorum index of the acknowledgements
(`JCommittedIdx` of the two voter halves) confirmed and answered. (Until 2026-10-14 also
`ReadAckResult`, at a simple configuration.) -/
def ReadAckResultC (c : CfgM) (id : w64) (s : NState) (src : w64) (ctx : List w8)
    (s' : NState) : Prop :=
  ∃ N, JCommittedIdx c.incoming c.outgoing
      (fun v => ((readonlyRecvAck s.rd.ro src ctx).acks !! v).getD (W64 0)) N ∧
    s' = readRespondAll id
      { s with rd := { s.rd with ro := (readonlyAdvance (readonlyRecvAck s.rd.ro src ctx) N).1 } }
      (readonlyAdvance (readonlyRecvAck s.rd.ro src ctx) N).2

/-- (2026-10-20, witness support) The check-quorum's new subterm: at a configuration with a
witness, `ChangeReplicationSet` swaps the excluded voter (`ChangeEpochOk`), the empty entry is
appended at the next subterm (`maybeStartNewSubterm`, `subtermStart`), and the `Visit` clears
`RecentActive`, which no record holds (`Match` kept). -/
def CQNewSub (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  ∃ (pvs : GMap w64 Progress) (em' : EpochM), c.wit ≠ W64 0 ∧ s.ep.hasWit = true ∧
    ChangeEpochOk c.incoming c.outgoing c.wit (W64 0) s.ep em' ∧
    prvalsMatch pvs = prvalsMatch s.prvals ∧
    s' = { subtermStart id { s with ep := em' } with prvals := pvs }

/-- (2026-10-20) A new subterm appends its entry: the unstable log grows. -/
theorem CQNewSub.uents {c : CfgM} {id : w64} {s s' : NState} (H : CQNewSub c id s s') :
    s'.logst.uents.length = s.logst.uents.length + 1 := by
  obtain ⟨pvs, em', -, -, -, -, rfl⟩ := H
  simp [subtermStart, sendMsgs, logAppend]

/-- What `stepLeader` does with `m` at the configuration `c`, for the types other than
`MsgProp` (none of which drops anything). The disjuncts are exclusive on `m.Type`. The read
path's confirmation and the commit are joint (`ReadAckResultC`, `AppRespAcceptedC`); a
read-index request (2026-10-12) is pending until an entry of the term is committed, then
`sendMsgReadIndexResponse`'s (`SendRIResult`: since 2026-10-14 answered at once at a
configuration whose only voter is the leader itself). (Until 2026-10-14 also
`LeaderNonpropResult`, at a simple configuration.) -/
def LeaderNonpropResultC (c : CfgM) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (s' : NState) : Prop :=
  ((m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
    m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp ∨
    m.Type' = MsgReadIndexResp) ∧
   s' = s) ∨
  (m.Type' = MsgBeat ∧
   ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs s ms with prvals := pvs } ∧
     (∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧ HbCtxOk s.rd.ro m'.ctx) ∧
     prvalsMatch pvs = prvalsMatch s.prvals) ∨
  (m.Type' = MsgHeartbeatResp ∧
   ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     ReplSends id s ms ∧
     prvalsMatch pvs = prvalsMatch s.prvals ∧
     ((ctx = [] ∨ m.From' ∉ domSet s.progress) ∧ s' = { sendMsgs s ms with prvals := pvs } ∨
      ctx ≠ [] ∧ ReadAckResultC c id { sendMsgs s ms with prvals := pvs } m.From' ctx s')) ∨
  (m.Type' = MsgReadIndex ∧
   ((plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed ≠ some s.term ∧
     s' = { s with rd := { s.rd with pend := s.rd.pend ++ [(m, ents)] } }) ∨
    (plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed = some s.term ∧
     SendRIResult c id s m ents s'))) ∨
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
     AppRespAcceptedC c id s m.From' m.Index' s'))) ∨
  ((m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
    m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader) ∧
   ∃ (lt' : w64) (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs { s with lt := lt' } ms with prvals := pvs } ∧
     ReplSends id s ms ∧
     prvalsMatch pvs = prvalsMatch s.prvals) ∨
  -- (2026-10-17, `CheckQuorum` on) the quorum check: the leader stays, or steps down at its
  -- term with no leader known (`becomeFollower(r.Term, None)`, when the voters it heard from
  -- recently are no quorum); then every other peer's `RecentActive` is cleared, which no record
  -- holds
  (m.Type' = MsgCheckQuorum ∧
   ((∃ pvs : GMap w64 Progress,
     (prvalsMatch pvs = prvalsMatch s.prvals ∧ s' = { s with prvals := pvs }) ∨
     s' = { becomeFollower s s.term (W64 0) with prvals := pvs }) ∨
    -- (2026-10-20, witness support) or, the quorum active, a new subterm
    CQNewSub c id s s'))

/-- What `stepLeader` does with `m` at the configuration `c`, by type. `dropped` is whether it
returned `ErrProposalDropped` (as in `FollowerStepResult`, `Spec/stepFollower.lean`); only a
`MsgProp` can be. The conf-change loop is judged at `c.joint`. (Until 2026-10-14 also
`LeaderStepResult`, at a simple configuration.) -/
def LeaderStepResultC (c : CfgM) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (dropped : Bool) (s' : NState) (ctx : List w8 := []) : Prop :=
  if m.Type' = MsgProp then
    LeaderProposeResult id s ents dropped s' c.joint
  else dropped = false ∧ LeaderNonpropResultC c id s m ents ctx s'

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
- `m.From ≠ 0` on `MsgAppResp`: `sendTimeoutNow` is dead (`leadTransferee = 0`);
- `m.From ≠ id` where `sendAppend(m.From)` can run: `send`'s self-addressed `Panicf`.
  An accepting `MsgAppResp` may come from the node itself (`appendEntry`'s
  self-acknowledgement): the code guards every send to `m.From` by `r.id != m.From`
  there;
- `Hctx`: a `MsgHeartbeatResp`'s `Context` holds `ctx` (stage R4: the message's state, `"Hm"`),
  empty or at least eight bytes (`recvAck`'s `Uint64`), a position sent
  (`maybeAdvance`'s bound); `Hrents`: a `MsgReadIndex`'s entries;
- `MsgProp`: a non-empty batch (`Panicf` otherwise) of fewer than `2^61` entries
  (`appendEntry`'s no-wrap bound), `Hents`: the batch at full ownership, since the
  conf-change loop writes refused entries and `appendEntry` stamps it in place, and (since
  2026-10-13) `Hcc`: each conf-change entry's bytes, which decode (`Unmarshal`'s
  `panic`). The batch comes back, changed, in the postcondition. (Stage R4: the batch is the
  message's (`"Hm"`, entry pointers at `1`: the loop replaces refused entries' slots);
  `appendEntry` clones it; nothing comes back.)

At any configuration since 2026-10-14 (reconfiguration stage A3): the struct at `c`
(`ownRaftPhysCV c c.voters`); the read path's confirmation is the joint quorum index of the
acknowledgements (`ReadAckResultC`, `maybeAdvance` on both voter halves), a commit is by a
joint quorum (`AppRespAcceptedC`), the conf-change loop judges `alreadyJoint` (`c.joint`:
inside a joint configuration only a request to leave it is accepted, outside one only a
change), and `RdOk` is over the voters of either half. A read-index request at a single voter
(until 2026-10-14 out of scope by a premise, `IsSingleton`'s immediate answer) is in scope since
the pinned raft has the fix of `issues/raft-readindex-singleton-stale.md`: the shortcut is in
`sendMsgReadIndexResponse`, after `committedEntryInCurrentTerm`, and only for the leader as the
single voter. (Until 2026-10-14 also `stepLeader.specS`, at a simple configuration; no
caller.) -/
abbrev stepLeader.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (k0 : Nat),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgBeat ∨
   m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨
   m.Type' = MsgProp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨
    m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgCheckQuorum)) →
  s.role = .leader →
  (m.Type' = MsgAppResp → m.From' ≠ W64 0) →
  (m.Type' = MsgHeartbeatResp ∨ (m.Type' = MsgAppResp ∧ m.Reject' = true) →
   m.From' ≠ id) →
  (m.Type' = MsgProp →
   ents ≠ [] ∧
   (ents.length : Int) < 2^61 ∧
   -- the leader's term is nonzero (2026-10-10; `appendEntry`'s premise, from the
   -- ghost state: `ownRaftGhost_term_nz`)
   s.term ≠ W64 0) →
  -- read-index (2026-10-12): the read-only state as the ghost state keeps it, the
  -- leader's term nonzero (`committedEntryInCurrentTerm`), a request with entries, and a
  -- heartbeat response's context a position sent (eight bytes)
  -- (2026-10-13: only for the three types whose paths read them; until 2026-10-14 also not
  -- at a single voter)
  (m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgReadIndex →
   RdOk c.voters s.rd ∧ s.term ≠ W64 0) →
  (m.Type' = MsgReadIndex → ents ≠ []) →
  (m.Type' = MsgHeartbeatResp →
   (ctx = [] ∨ 8 ≤ ctx.length) ∧
   (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                 ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int))) →
  -- (2026-10-16, stage R8a, D11) an accepted `MsgAppResp` acknowledges an index within the
  -- leader's log, so `MaybeUpdate` keeps the leader's progress bound (`PrvalsOk`): `Step` has it
  -- from the message's ghost witness (`ackIn`, `ownRaftGhost_ackIn_le`)
  -- (2026-10-19, D21 M3) and in the no-snapshot mode a rejecting `MsgAppResp` rejects an index
  -- past `1` with a hint in `[1, Index]` (`isMessage`'s clause, the bootstrap log being in every
  -- log), and the leader's term at index `1` is at most `1` (the bootstrap log's): `MaybeDecrTo`
  -- keeps `Next ≥ 2` (`PrLo`)
  (m.Type' = MsgAppResp →
    (m.Reject' = false → uint.Z m.Index' ≤ uint.Z (logLast s.logst)) ∧
    (m.Reject' = true → s.gh.ns = true →
      2 ≤ uint.Z m.Index' ∧ 1 ≤ uint.Z m.RejectHint' ∧ uint.Z m.RejectHint' ≤ uint.Z m.Index' ∧
      (∀ t0, plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) (W64 1) = some t0 →
        uint.Z t0 ≤ 1))) →
  -- (2026-10-19, D21 M2r) a transfer request only with leader transfer on (`NGhost.xf`)
  (m.Type' = MsgTransferLeader → s.gh.xf = false) →
  -- (2026-10-20, witness support) at a check-quorum, the leader's term nonzero (a new subterm's
  -- entry, `appendEntry`'s premise; from the ghost state: `ownRaftGhost_term_nz`)
  (m.Type' = MsgCheckQuorum → s.term ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (stage R4) the message, as `Step` received it: its entry pointers owned for a
      -- `MsgProp`, read-only otherwise
      "Hm" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
               ⟨m, ents, sn, ctx, rs⟩ ∗
      -- (2026-10-13) and its conf-change entries' bytes, which decode
      "Hcc" ∷ (⌜m.Type' = MsgProp⌝ -∗ ∃ cs, ccEntsOk ents cs) ∗
      -- (2026-10-18, D19b stage 5) a time receipt, raised by one per entry of an appended
      -- proposal (`appendEntry`'s)
      "#Hrc" ∷ ⧖ k0 }}
    (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhysCV c c.voters r id s' ∗
      -- the receipt raised by the entries appended: an appended proposal's, or (2026-10-20,
      -- witness support) a check-quorum's new subterm's
      (⌜(m.Type' = MsgProp ∧ dropped = false) ∨
          (m.Type' = MsgCheckQuorum ∧ CQNewSub c id s s')⌝ -∗
        ⧖ (k0 + if m.Type' = MsgProp then ents.length else 1)) ∗
      ⌜LeaderStepResultC c id s m ents dropped s' ctx⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}


end spec

end EtcdGrove
end Perennial
