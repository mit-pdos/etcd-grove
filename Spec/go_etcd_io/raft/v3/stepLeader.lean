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
- `MsgReadIndex` (2026-10-12): not at a single voter (premise), pending until an entry of
  the leader's term is committed (`committedEntryInCurrentTerm`), then
  `sendMsgReadIndexResponse`.
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
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
-- read-index (2026-10-12)
public import Spec.go_etcd_io.raft.v3.releasePendingReadIndexMessages
public import Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- `releasePendingReadIndexMessages`' heartbeats at `s` (2026-10-12): `HeartbeatOk`, each
with the position after one of the released requests. -/
def ReleaseHbs (id : w64) (s : NState) (hb : List Msg) : Prop :=
  ∀ m' ∈ hb, HeartbeatOk id (toPState s) m' ∧
    ∃ k, 0 < k ∧ k ≤ s.rd.pend.length ∧
      m'.ctx = hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k))

/-- `MsgAppResp` accepted from `src` at `index`: `s'` is `s` with the sender's `Match`
raised as `MaybeUpdate` raises it (the `Progress` values are otherwise unconstrained:
`pvs`), `committed` at `c` -- unchanged, or a `CommitOk` index judged against the
raised `Match` map -- and the outbox grown by `ms`, which `ReplSends` allows after the
commit. (Rocq's argument `from` is `src`.) -/
def AppRespAccepted (cfg : GSet w64) (id : w64) (s : NState) (src index : w64)
    (s' : NState) : Prop :=
  ∃ (x : w64) (pvs : GMap w64 Progress) (c : w64) (hb ms : List Msg),
    prvalsMatch s.prvals !! src = some x ∧
    prvalsMatch pvs =
      <[src := if uint.Z x < uint.Z index then index else x]> (prvalsMatch s.prvals) ∧
    (c = s.logst.committed ∨
     CommitOk cfg (toPState { s with prvals := pvs }) c) ∧
    ReplSends id { s with logst := { s.logst with committed := c } } ms ∧
    -- (2026-10-12) a commit releases the pending read-index requests, with their
    -- heartbeats `hb` (judged, 2026-10-13, at the raised `Match` map: a heartbeat's
    -- `Commit` is `min(Match, committed)` of the `Progress` it is sent from)
    (if c = s.logst.committed then hb = [] ∧
       s' = { sendMsgs { s with logst := { s.logst with committed := c } } ms with
                prvals := pvs }
     else ReleaseHbs id { s with logst := { s.logst with committed := c }, prvals := pvs } hb ∧
       s' = { sendMsgs (sendMsgs (releasedState id
                { s with logst := { s.logst with committed := c } }) hb) ms with
                prvals := pvs })

/-- A confirmed read-index request answered (2026-10-12, `responseToReadIndexReq` and the
`send`): a local one becomes a `ReadState` (its context the first entry's data), a
forwarded one a `MsgReadIndexResp` to its sender. -/
def readRespond (id : w64) (s : NState) (q : ReadReq) : NState :=
  if q.src = W64 0 ∨ q.src = id then
    match q.ents with
    | e :: _ => addReadState s q.index e.Data'
    | [] => s
  else sendMsgs s [Msg.mk .readIndexResp id q.src s.term false q.index (W64 0) (W64 0)
                     (W64 0) q.ents]

def readRespondAll (id : w64) (s : NState) (qs : List ReadReq) : NState :=
  qs.foldl (readRespond id) s

/-- The read path of a `MsgHeartbeatResp` with a context (2026-10-12): the sender's
acknowledgement, the requests a quorum has acknowledged confirmed and answered. -/
def ReadAckResult (cfg : GSet w64) (id : w64) (s : NState) (src : w64) (ctx : List w8)
    (s' : NState) : Prop :=
  ∃ N, IsQuorumIndex cfg (fun v => ((readonlyRecvAck s.rd.ro src ctx).acks !! v).getD (W64 0)) N ∧
    s' = readRespondAll id
      { s with rd := { s.rd with ro := (readonlyAdvance (readonlyRecvAck s.rd.ro src ctx) N).1 } }
      (readonlyAdvance (readonlyRecvAck s.rd.ro src ctx) N).2

/-- The state `appendEntry` leaves when it accepts the batch `ents`: the log grows by
the stamped batch (`stamp`, the term and the indices after the last), and the
self-acknowledgement at the new last index is queued -- `Step.propose`'s state, under
`NStateRel`. -/
def proposed (id : w64) (s : NState) (ents : List raftpb.Entry) : NState :=
  let s1 :=
    { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }
  sendMsgs s1 [selfAck id s1]

/-- `stepLeader`'s conf-change loop at `s` (2026-10-13): the batch it leaves and
`pendingConfIndex` (`propConf`, `CCModel.lean`), for the decoded conf changes `cs`. -/
def leaderPropConf (s : NState) (ents : List raftpb.Entry) (cs : List (Option CCMsg)) :
    List raftpb.Entry × w64 :=
  propConf s.logst.applied (logLast s.logst) s.pci ents cs

/-- `MsgProp` at the leader: dropped -- unchanged (a leader transfer in progress, before
the conf-change loop), or with only `pendingConfIndex` moved by the loop (`appendEntry`
refused the batch) -- or the loop's batch appended and then `bcastAppend`'s sends, judged
at the appended state, with no `Match` moved; for some decoded conf changes `cs` of the
batch (2026-10-13; until then the batch was appended as proposed). -/
def LeaderProposeResult (id : w64) (s : NState) (ents : List raftpb.Entry)
    (dropped : Bool) (s' : NState) : Prop :=
  ∃ cs : List (Option CCMsg), CCTypesOk ents cs ∧
  if dropped then s' = s ∨ s' = { s with pci := (leaderPropConf s ents cs).2 }
  else ∃ (ms : List Msg) (pvs : GMap w64 Progress),
    s' = { sendMsgs (proposed id { s with pci := (leaderPropConf s ents cs).2 }
             (leaderPropConf s ents cs).1) ms with prvals := pvs } ∧
    ReplSends id (proposed id { s with pci := (leaderPropConf s ents cs).2 }
      (leaderPropConf s ents cs).1) ms ∧
    prvalsMatch pvs = prvalsMatch s.prvals

/-- What `stepLeader` does with `m`, for the types other than `MsgProp` (none of which
drops anything). The disjuncts are exclusive on `m.Type`. -/
def LeaderNonpropResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8) (s' : NState) : Prop :=
  ((m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
    m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp ∨
    -- (2026-10-13) a read-index response, at a leader of its term (which the protocol
    -- excludes): in neither switch
    m.Type' = MsgReadIndexResp) ∧
   s' = s) ∨
  (m.Type' = MsgBeat ∧
   ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs s ms with prvals := pvs } ∧
     -- (2026-10-13) with the read-only object's context
     (∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧ HbCtxOk s.rd.ro m'.ctx) ∧
     prvalsMatch pvs = prvalsMatch s.prvals) ∨
  (m.Type' = MsgHeartbeatResp ∧
   ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     ReplSends id s ms ∧
     prvalsMatch pvs = prvalsMatch s.prvals ∧
     -- (2026-10-12) the read path, for a context
     -- (no read path without a context, or for a sender with no `Progress`)
     ((ctx = [] ∨ m.From' ∉ domSet s.progress) ∧ s' = { sendMsgs s ms with prvals := pvs } ∨
      ctx ≠ [] ∧ ReadAckResult cfg id { sendMsgs s ms with prvals := pvs } m.From' ctx s')) ∨
  -- (2026-10-12) a read-index request: pending until an entry of the term is committed,
  -- then queued and heartbeats broadcast
  (m.Type' = MsgReadIndex ∧
   ((plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed ≠ some s.term ∧
     s' = { s with rd := { s.rd with pend := s.rd.pend ++ [(m, ents)] } }) ∨
    (plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed = some s.term ∧
     ∃ (ms : List Msg) (pvs : GMap w64 Progress),
       s' = { sendMsgs (arriveState id s m ents) ms with prvals := pvs } ∧
       (∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
          m'.ctx = hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents))) ∧
       prvalsMatch pvs = prvalsMatch s.prvals))) ∨
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
     AppRespAccepted cfg id s m.From' m.Index' s'))) ∨
  -- (2026-10-13) `ForgetLeader` and `MsgTimeoutNow` (no-ops), the local reports (a peer's
  -- `Progress` state, not its `Match`) and a leader-transfer request (`leadTransferee`,
  -- and a `sendAppend` to the transferee; its `MsgTimeoutNow` drops out of the outbox)
  ((m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
    m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader) ∧
   ∃ (lt' : w64) (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs { s with lt := lt' } ms with prvals := pvs } ∧
     ReplSends id s ms ∧
     prvalsMatch pvs = prvalsMatch s.prvals)

/-- What `stepLeader` does with `m`, by type. `dropped` is whether it returned
`ErrProposalDropped` (as in `FollowerStepResult`, `Spec/stepFollower.lean`); only a
`MsgProp` can be. -/
def LeaderStepResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) (ctx : List w8 := []) : Prop :=
  if m.Type' = MsgProp then
    LeaderProposeResult id s ents dropped s'
  else dropped = false ∧ LeaderNonpropResult cfg id s m ents ctx s'

/-- What the read-index code needs of the read-only state (2026-10-12; the ghost state,
`ownReadGhost`, keeps it): every voter's acknowledgement is a position sent (at most the
queue's end, so `maybeAdvance` does not panic), and every request has entries (its
context is the first's data). -/
def RdOk (cfg : GSet w64) (rd : RdState) : Prop :=
  (∀ v ∈ cfg, uint.Z ((rd.ro.acks !! v).getD (W64 0))
                ≤ uint.Z rd.ro.confirmed + (rd.ro.pending.length : Int)) ∧
  (∀ q ∈ rd.ro.pending, q.ents ≠ []) ∧
  (∀ p ∈ rd.pend, p.2 ≠ [])

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
- `Hctx`: a `MsgHeartbeatResp`'s `Context` holds `ctx` (for any other type the wand is
  trivial), empty or at least eight bytes (`recvAck`'s `Uint64`), a position sent
  (`maybeAdvance`'s bound); `Hrents`: a `MsgReadIndex`'s entries;
- `MsgProp`: a non-empty batch (`Panicf` otherwise) of fewer than `2^61` entries
  (`appendEntry`'s no-wrap bound), `Hents`: the batch at full ownership, since the
  conf-change loop writes refused entries and `appendEntry` stamps it in place, and (since
  2026-10-13) `Hcc`: each conf-change entry's bytes, which decode (`Unmarshal`'s
  `panic`). The batch comes back, changed, in the postcondition. -/
abbrev stepLeader.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgBeat ∨
   m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨
   m.Type' = MsgProp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨
    m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader)) →
  s.role = .leader →
  id ∈ cfg →
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
  -- leader's term nonzero (`committedEntryInCurrentTerm`), a request not at a single voter
  -- (`IsSingleton`'s immediate, unconfirmed answer is out of scope) and with entries, and a
  -- heartbeat response's context a position sent (eight bytes)
  -- (2026-10-13: only for the three types whose paths read them)
  (m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgReadIndex →
   RdOk cfg s.rd ∧ s.term ≠ W64 0) →
  (m.Type' = MsgReadIndex → 1 < GMap.size cfg ∧ ents ≠ []) →
  (m.Type' = MsgHeartbeatResp →
   (ctx = [] ∨ 8 ≤ ctx.length) ∧
   (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                 ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hctx" ∷ (⌜m.Type' = MsgHeartbeatResp⌝ -∗ m.Context' ↦*□ ctx) ∗
      -- (2026-10-13) and its conf-change entries' bytes, which decode
      "Hents" ∷ (⌜m.Type' = MsgProp⌝ -∗
                 m.Entries' ↦* ents ∗ ∃ cs, ccEntsOk ents cs) ∗
      "Hrents" ∷ (⌜m.Type' = MsgReadIndex⌝ -∗ m.Entries' ↦*□ ents) }}
    (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhys cfg r id s' ∗
      ⌜LeaderStepResult cfg id s m ents dropped s' ctx⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) ∗
      -- the batch, changed (refused conf changes overwritten, stamped) -- or untouched,
      -- when a leader transfer in progress dropped it before the loop (2026-10-13: until
      -- then stated exactly; no caller used it)
      (⌜m.Type' = MsgProp⌝ -∗ ∃ ents' : List raftpb.Entry, m.Entries' ↦* ents') }}

end spec

end EtcdGrove
end Perennial
