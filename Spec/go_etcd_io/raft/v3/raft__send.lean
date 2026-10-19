/-
Port of `election_proof/spec_raft__send.v` (feb5c73d4).

## `raft.send`

`send` is the only place a message reaches the network, so this is where the abstract
outbox grows. What the body does, in order (`raft.send.impl` in
`Code/go_etcd_io/raft/v3.lean`):

1. `From`, if unset, becomes `r.id`. (Since 2026-10-06 `send` may also be given a
   message whose `From` is already `r.id`.)
2. For a vote request/response (`MsgVote`, `MsgVoteResp`, `MsgPreVote`,
   `MsgPreVoteResp`) the caller must have set `Term`: zero is a `Panicf`. For every
   other type `Term` must be *unset* (non-zero is a `Panicf`), and `send` then stamps
   `r.Term` into it -- except for `MsgProp` and `MsgReadIndex`, which are forwarded
   with `Term = 0`.
3. Responses (`MsgAppResp`, `MsgVoteResp`, `MsgPreVoteResp`) are queued on
   `r.msgsAfterAppend`; everything else on `r.msgs`, after a `Panicf` if it is
   self-addressed.
4. `traceSendMessage`.

The model has a single outbox, so the routing is invisible here: the abstract outbox
grows by `out`, the abstraction of the message as queued (`absMsgFrom` of the stamped
message), given case by case by `SendOk` below. There is no `isMessage` precondition:
`send` does not have to know the message is protocol-legal, it only records that the
node put it in its outbox. Legality is established once, by `Step`, against
`ownRaftGhost`.

Lean notes: Rocq's `send_ok` is `SendOk` (a Prop-valued definition). The Rocq
clause-selection recipes are kept as written; in Lean they are `Or.inl`/`Or.inr` and
the anonymous constructor.

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`), owned (`msgOwn ml 1`: a message
the caller built, or a forwarded one frozen by `msgIn_to_msgOwn`), read through its getters;
`send` writes `m.From = new(r.id)` and `m.Term = new(r.Term)` and queues the pointer, which the
outbox then owns (`outboxRel`'s `msgQ`). `SendOk` is the old statement over the record's scalars
(`MessageM`) with "`Entries`/`Context` `nil`" as `ents = []`/`ctx = []`; the `MsgSnap` clause's
`"Hsnap"` (the snapshot behind `m.Snapshot` and its voters, read through the heap) is now the pure
premise `SnapOut`: the message holds a snapshot `sv` (`sn = some sv`) and `out` is its
abstraction, at the lists of its `ConfState` (`sv.Metadata'.ConfState'.lists`, which `msgAbs`
uses for a queued `MsgSnap`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section send_ok
variable [FfiSyntax]

/-- `SendOk id s m ents out`: the message `m`, whose `Entries` slice holds `ents`, takes
a non-panicking path through `send` on a node with id `id` in state `s`, and `out` is
what the abstract outbox grows by -- the abstraction of the message as queued, i.e. of
`m` with `From := id` and `Term` as `send` leaves it (`absMsgFrom`, `Defs.lean`). One
clause per shape a caller builds:

(a) a vote request/response (`MsgVote`, `MsgVoteResp`, and since 2026-10-04
    `MsgPreVote`, `MsgPreVoteResp`). `Term` is the caller's and is kept. A request goes
    onto `r.msgs` and must not be self-addressed; a response may be, and then (since
    2026-10-10) carries no `Entries` and no `Context` and is not from a later term than
    the node's -- one later for a `MsgPreVoteResp`, a pre-campaign's own -- which is what
    `ownRaftPhys` records of a self-addressed response (`AAMsgOk`, `InvRaftPhys.lean`)
    for `RawNode.Advance` to step it. Its term is at most the node's or within its term
    ceiling (`OutTermOk`, which `ownRaftPhys` records of every queued message; 2026-10-17,
    until then with pre-vote off at most the node's): a pre-campaign's request, a granted
    pre-vote's response.
(b) a message stamped with the current term and queued on `r.msgs`: `MsgApp`,
    `MsgHeartbeat`, `MsgReadIndexResp`, `MsgHeartbeatResp`. `Term` must be unset; the
    abstract message carries `s.term`, which is what `send` stamps in
    (`r.Term = s.term` by `ownRaftPhys`). Not self-addressed (`Panicf`). (`MsgSnap` was
    here until 2026-10-02; it has its own clause now, (c'). `MsgReadIndexResp`, which
    nothing in scope sends, takes exactly this path through the body and holds its
    place, so that a caller's `by right; right; right` still picks `MsgHeartbeatResp`.)
(c) a message the model does not describe (`mtypeOf = none`). It is queued and drops
    out of the abstract outbox. `Term` unset, not self-addressed. (2026-10-19, D21 M2r) Only
    with leader transfer on (`NGhost.xf = false`): raft sends two such types, `MsgTimeoutNow`
    and a forwarded `MsgTransferLeader`, both of a transfer.
(c') `MsgSnap` (2026-10-02): stamped and queued like (b), but the abstract message is
    `absSnapFrom` of the snapshot `m.Snapshot` points to and of that snapshot's
    `ConfState.Voters`. `send` does not read the pointer, so the caller names the two
    and supplies their read-only points-tos: the precondition's `"Hsnap"` fixes
    `out = [absSnapFrom m id s.term sv voters]` for exactly those `sv`/`voters` (since
    2026-10-03; until then the clause itself said `∃ sv voters, out = ...`, untied to
    the heap). (Stated as the left disjunct of (c), which no caller uses, so that no
    caller's clause selection moved.)
(d) `MsgAppResp`: stamped like (b), but a response, so it goes onto
    `r.msgsAfterAppend` and may be self-addressed (`appendEntry`'s self-acknowledgement
    is) -- and then (since 2026-10-10) carries no `Entries` and no `Context`, does not
    reject, and the node's term is nonzero (`AAMsgOk`, as for (a)).
(e) `MsgProp`, forwarded to the leader: `Term` must be unset and stays `0` (the body's
    `MsgProp`/`MsgReadIndex` exception); onto `r.msgs`, not self-addressed. And
    (2026-10-12) `MsgReadIndex`, forwarded the same way (the right disjunct).

`ctx` (2026-10-12) is the list `m.Context` holds (the precondition's `"Hctx"`), which the
abstract message carries.
Until 2026-10-01 `MsgAppResp`, `MsgSnap` and `MsgHeartbeatResp` were under (c),
invisible to the model. -/
def SendOk (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (ctx : List w8) (out : List Msg) : Prop :=
  (∃ ty,
     (m.Type' = MsgVote ∨ m.Type' = MsgVoteResp ∨
      m.Type' = MsgPreVote ∨ m.Type' = MsgPreVoteResp) ∧
     mtypeOf m.Type' = some ty ∧
     m.Term' ≠ W64 0 ∧
     (m.Type' = MsgVote ∨ m.Type' = MsgPreVote → m.To' ≠ id) ∧
     (m.To' = id →
        ents = [] ∧ ctx = [] ∧
        uint.Z m.Term' ≤ uint.Z s.term + (if m.Type' = MsgPreVoteResp then 1 else 0)) ∧
     -- (2026-10-17) at most the node's term or the ceiling (`NGhost.tc`)
     (uint.Z m.Term' ≤ uint.Z s.term ∨ uint.Z m.Term' ≤ uint.Z s.gh.tc) ∧
     out = [absMsgFrom ty m id m.Term' ents ctx])
  ∨
  (∃ ty,
     (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
      m.Type' = MsgReadIndexResp ∨
      m.Type' = MsgHeartbeatResp) ∧
     mtypeOf m.Type' = some ty ∧
     m.Term' = W64 0 ∧
     m.To' ≠ id ∧
     out = [absMsgFrom ty m id s.term ents ctx])
  ∨
  ((m.Type' = MsgSnap ∧
    m.Term' = W64 0 ∧
    m.To' ≠ id ∧
    -- (2026-10-19, D21 M3) not in the no-snapshot mode
    s.gh.ns = false)
   ∨
   (mtypeOf m.Type' = none ∧
    m.Term' = W64 0 ∧
    m.To' ≠ id ∧
    out = [] ∧
    -- (2026-10-19, D21 M2r) only with leader transfer on (`NGhost.xf`): the types the model does
    -- not describe that raft sends are `MsgTimeoutNow` and a forwarded `MsgTransferLeader`
    s.gh.xf = false))
  ∨
  (m.Type' = MsgAppResp ∧
   m.Term' = W64 0 ∧
   (m.To' = id →
      ents = [] ∧ ctx = [] ∧ s.term ≠ W64 0 ∧
      m.Reject' = false) ∧
   out = [absMsgFrom .appResp m id s.term ents ctx])
  ∨
  ((m.Type' = MsgProp ∧
    m.Term' = W64 0 ∧
    m.To' ≠ id ∧
    out = [absMsgFrom .propose m id (W64 0) ents ctx])
   ∨
   (m.Type' = MsgReadIndex ∧
    m.Term' = W64 0 ∧
    m.To' ≠ id ∧
    out = [absMsgFrom .readIndex m (if m.From' = W64 0 then id else m.From') (W64 0) ents ctx]))

/- A caller discharges `SendOk` by picking the clause and splitting it: for a vote
message with `ty` the abstract type, in Rocq,

    left; exists ty; split_and!;
      [by right; left | apply mtype_of_MsgVoteResp | <Term ≠ 0>
       | intros [Hc|Hc]; revert Hc; w32_ne | <self> | done]

(the fourth discharges the request clause for a response type; `<self>` is the
self-addressed response's clause, vacuous for a request, `To ≠ id`)

(the last `done` fixes `out`); for a `MsgApp`, `right; left; exists mtype.App;
split_and!; [by left | .. | done | <To ≠ id> | done]`; for `MsgAppResp`,
`right; right; right; left; split_and!; [done | done | <self> | done]`; for `MsgSnap`,
`right; right; left; left; split_and!; [done | done | <To ≠ id>]`. These are not lemmas
here because a spec file states and does not prove (etc/check-module-discipline.py,
F3).

**`ents`.** `m.Entries ↦*□ ents` is a precondition: it is what `ownRaftPhys` keeps for
the queued message (`outboxRel`, `InvRaftPhys.lean`). For a message built without
`Entries` the field is `slice.nil` and `ents = []` (`ownSlice_nil`). (Stage R4: the message's
state, `msgOwn ml 1 ⟨m, ents, sn, ctx, rs⟩`, ties `ents` and `ctx` to the heap.)

**`"Hsnap"`** (2026-10-03): for a `MsgSnap`, the snapshot `sv` that `m.Snapshot` points
to and its `ConfState.Voters` list `voters`, both read-only, and `out` is the
abstraction at those -- what `ownRaftPhys` keeps for the queued message (`msgAbs`).
Every other caller discharges it from its message type (`send_no_snap`,
`InvRaftPhys.lean`). (Stage R4: the pure premise `SnapOut` below; a caller of another type
discharges it by its message type.) -/

/-- The `MsgSnap` premise of `send` (stage R4): the message holds a snapshot `sv` and `out` is
its abstraction, at the lists of its `ConfState` (what `msgAbs` uses for a queued `MsgSnap`). -/
def SnapOut (id : w64) (s : NState) (m : MessageM) (sn : Option SnapshotM)
    (out : List Msg) : Prop :=
  m.Type' = MsgSnap →
    ∃ sv, sn = some sv ∧ out = [absSnapFrom m id s.term sv sv.Metadata'.ConfState'.lists]

end send_ok

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Stated on `ownRaftPhys`, for **any** `s`. `send` touches `r.msgs`,
`r.msgsAfterAppend`, `r.logger` and the tracing hook, and *reads* `r.id` and `r.Term`;
everything else in `s` -- the tracker's progress map and `Progress` values, the log --
comes back as it went in, because `sendMsgs` changes only the outbox.
`maybeSendAppend` relies on it: it reads a `Progress` before this call and needs it
unchanged after (`NState.prvals`), and holds `ents` (read-only) across it.

From 2026-09-21 to 2026-09-22 this was stated on a variant predicate, `own_raft_bare`;
see notes/decisions.md ("Three layers") and notes/false-statements.md, 2026-09-21. -/
abbrev raft.send.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (out : List Msg),
  -- `From` unset, or already the node's own (`RawNode.Propose` stamps `From: r.id`
  -- before `Step`; a follower forwards that proposal as it is). Either way the queued
  -- message has `From = id`.
  -- (2026-10-12) or a read-index request forwarded on, which keeps its requester
  -- (2026-10-13) or a leader-transfer request forwarded to the leader, which keeps its
  -- transferee
  (m.From' = W64 0 ∨ m.From' = id ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader) →
  SendOk id s m ents ctx out →
  SnapOut id s m sn out →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgOwn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (sendMsgs s out) }}

end spec

end EtcdGrove
end Perennial
