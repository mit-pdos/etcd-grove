/-
Port of `election_proof/spec_raft__send.v`.

## `raft.send`

`send` is the only place a message reaches the network, so this is where the abstract
outbox grows. What the body does, in order (`raft.send.impl` in
`Perennial/Code/go_etcd_io/raft/v3.lean`):

1. `From`, if unset, becomes `r.id`.
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
grows by `out`, the abstraction of the message as queued (`absMsgOpt` applied to the
stamped message), given case by case by `SendOk` below. There is no `isMessage`
precondition: `send` does not have to know the message is protocol-legal, it only
records that the node put it in its outbox. Legality is established once, by `Step`,
against `ownRaftGhost`.

Lean notes: Rocq's `send_ok` is `SendOk` (a Prop-valued definition), and its
`msg.mk ty from to term reject` is `Msg.mk ty src dst term reject`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The message-type constants the body compares against that `Defs.lean` does not name
(the model never sees these types). -/
def MsgProp : w32 := W32 2
def MsgReadIndex : w32 := W32 15

section send_ok
variable [FfiSyntax]

/-- `SendOk id s m out`: the message `m` takes a non-panicking path through `send` on a
node with id `id` in state `s`, and `out` is what the abstract outbox grows by. One
clause per shape a caller builds:

(a) a vote request/response. `Term` is the caller's and is kept.
(b) a leader message the model describes (`MsgApp`, `MsgHeartbeat`). `Term` must be
    unset; the abstract message carries `s.term`, which is what `send` stamps in
    (`r.Term = s.term` by `ownRaftPhys`).
(c) a message the model does not describe (`MsgAppResp`, `MsgSnap`, ...). It is queued,
    and drops out of the abstract outbox (`absMsgOpt` is `none`), so the abstract state
    is unchanged up to `sendMsgs s []`.

Only (a) and `MsgAppResp` under (c) may be self-addressed: `send` panics on any other
self-addressed message. The pre-vote types are excluded from (c) because their `Term`
discipline is (a)'s; `ownRaftPhys` has `preVote = false` anyway. -/
def SendOk (id : w64) (s : NState) (m : raftpb.Message) (out : List Msg) : Prop :=
  (∃ ty,
     (m.Type' = MsgVote ∨ m.Type' = MsgVoteResp) ∧
     mtypeOf m.Type' = some ty ∧
     m.Term' ≠ W64 0 ∧
     (m.Type' = MsgVote → m.To' ≠ id) ∧
     out = [Msg.mk ty id m.To' m.Term' m.Reject'])
  ∨
  (∃ ty,
     (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat) ∧
     mtypeOf m.Type' = some ty ∧
     m.Term' = W64 0 ∧
     m.To' ≠ id ∧
     out = [Msg.mk ty id m.To' s.term m.Reject'])
  ∨
  (mtypeOf m.Type' = none ∧
   m.Type' ≠ MsgPreVote ∧
   m.Type' ≠ MsgPreVoteResp ∧
   m.Term' = W64 0 ∧
   (m.To' = id → m.Type' = MsgAppResp) ∧
   out = [])

/- A caller discharges `SendOk` by picking the clause and splitting it: for a vote
message with `ty` the abstract type, in Rocq,

    left; exists ty; split_and!;
      [by right | apply mtype_of_MsgVoteResp | <Term ≠ 0> | w32_ne | done]

(the last `done` fixes `out`); for a `MsgApp`, `right; left; exists mtype.App;
split_and!; [by left | .. | done | <To ≠ id> | done]`; for a hidden type,
`right; right; split_and!; [.. | done]`. (In Lean: `Or.inl`/`Or.inr` and the anonymous
constructor, with `mtypeOf_MsgVoteResp` and `rfl`.) These are not lemmas here because a
spec file states and does not prove (etc/check-module-discipline.py, F3). -/

end send_ok

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Stated on `ownRaftPhys`, for **any** `s`. `send` touches `r.msgs`,
`r.msgsAfterAppend`, `r.logger` and the tracing hook, and *reads* `r.id` and `r.Term`;
everything else in `s` -- the tracker's progress map and `Progress` values, the log --
comes back as it went in, because `sendMsgs` changes only the outbox.
`maybeSendAppend` relies on it: it reads a `Progress` before this call and needs it
unchanged after (`NState.prvals`), and holds `ents` (read-only) across it. (Until
2026-09-29 the tracker was lent out of the predicate for that, `nstate.lent`.)

From 2026-09-21 to 2026-09-22 this was stated on a variant predicate, `own_raft_bare`,
which cut the tracker and the log out of the struct so that `maybeSendAppend` could
hold a `Progress` and `ents` across the call. That is exactly the pattern main's
notes/decisions.md ("Three layers") now rules out: the fix was to make `NState` say what
the variant said (`progress`, `log`, and then `prvals`). See main's
notes/false-statements.md, 2026-09-21, for why `ownRaftPhys` as it then was could not
state it. -/
abbrev raft.send.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (out : List Msg),
  m.From' = W64 0 →
  SendOk id s m out →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send")) (Val #m))
  {{ RET #(); ownRaftPhys cfg r id (sendMsgs s out) }}

end spec

end EtcdGrove
end Perennial
