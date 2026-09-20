Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** * [raft.send]

    [send] is the only place a message reaches the network, so this is where
    the abstract outbox grows.  What the body does, in order
    ([raft__sendⁱᵐᵖˡ] in new/code/go_etcd_io/raft/v3.v):

    1. [From], if unset, becomes [r.id].
    2. For a vote request/response ([MsgVote], [MsgVoteResp], [MsgPreVote],
       [MsgPreVoteResp]) the caller must have set [Term]: zero is a [Panicf].
       For every other type [Term] must be *unset* (non-zero is a [Panicf]),
       and [send] then stamps [r.Term] into it -- except for [MsgProp] and
       [MsgReadIndex], which are forwarded with [Term = 0].
    3. Responses ([MsgAppResp], [MsgVoteResp], [MsgPreVoteResp]) are queued
       on [r.msgsAfterAppend]; everything else on [r.msgs], after a [Panicf]
       if it is self-addressed.
    4. [traceSendMessage].

    The model has a single outbox, so the routing is invisible here: the
    abstract outbox grows by [out], the abstraction of the message as queued
    ([abs_msg_opt] applied to the stamped message), given case by case by
    [send_ok] below.  There is no [is_message] precondition: [send] does not
    have to know the message is protocol-legal, it only records that the node
    put it in its outbox.  Legality is established once, by [Step], against
    [own_raft_ghost]. *)

(** The message-type constants the body compares against that [defs.v] does
    not name (the model never sees these types). *)
Definition MsgProp : w32 := W32 2.
Definition MsgReadIndex : w32 := W32 15.

(** [send_ok id s m out]: the message [m] takes a non-panicking path through
    [send] on a node with id [id] in state [s], and [out] is what the abstract
    outbox grows by.  One clause per shape a caller builds:

    (a) a vote request/response.  [Term] is the caller's and is kept.
    (b) a leader message the model describes ([MsgApp], [MsgHeartbeat]).
        [Term] must be unset; the abstract message carries [s.term], which is
        what [send] stamps in ([r.Term = s.term] by [own_raft_phys]).
    (c) a message the model does not describe ([MsgAppResp], [MsgSnap], ...).
        It is queued, and drops out of the abstract outbox ([abs_msg_opt]
        is [None]), so the abstract state is unchanged up to [send_msgs s []].

    Only (a) and [MsgAppResp] under (c) may be self-addressed: [send] panics
    on any other self-addressed message.  The pre-vote types are excluded
    from (c) because their [Term] discipline is (a)'s; [own_raft_phys] has
    [preVote = false] anyway. *)
Definition send_ok (id : w64) (s : nstate.t) (m : raftpb.Message.t)
    (out : list msg.t) : Prop :=
  (∃ ty,
     (m.(raftpb.Message.Type') = MsgVote ∨ m.(raftpb.Message.Type') = MsgVoteResp) ∧
     mtype_of m.(raftpb.Message.Type') = Some ty ∧
     m.(raftpb.Message.Term') ≠ W64 0 ∧
     (m.(raftpb.Message.Type') = MsgVote → m.(raftpb.Message.To') ≠ id) ∧
     out = [msg.mk ty id m.(raftpb.Message.To')
              m.(raftpb.Message.Term') m.(raftpb.Message.Reject')])
  ∨
  (∃ ty,
     (m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgHeartbeat) ∧
     mtype_of m.(raftpb.Message.Type') = Some ty ∧
     m.(raftpb.Message.Term') = W64 0 ∧
     m.(raftpb.Message.To') ≠ id ∧
     out = [msg.mk ty id m.(raftpb.Message.To')
              s.(nstate.term) m.(raftpb.Message.Reject')])
  ∨
  (mtype_of m.(raftpb.Message.Type') = None ∧
   m.(raftpb.Message.Type') ≠ MsgPreVote ∧
   m.(raftpb.Message.Type') ≠ MsgPreVoteResp ∧
   m.(raftpb.Message.Term') = W64 0 ∧
   (m.(raftpb.Message.To') = id → m.(raftpb.Message.Type') = MsgAppResp) ∧
   out = []).

(** A caller discharges [send_ok] by picking the clause and splitting it:
    for a vote message with [ty] the abstract type,

      left; exists ty; split_and!;
        [by right | apply mtype_of_MsgVoteResp | <Term ≠ 0> | w32_ne | done]

    (the last [done] fixes [out]); for a [MsgApp], [right; left; exists
    mtype.App; split_and!; [by left | .. | done | <To ≠ id> | done]]; for a
    hidden type, [right; right; split_and!; [.. | done]].  These are not
    lemmas here because a spec file states and does not prove
    (etc/check-module-discipline.py, F3). *)

Definition wp_raft__send_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t) (out : list msg.t),
  m.(raftpb.Message.From') = W64 0 →
  send_ok id s m out →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "send" #m
  {{{ RET #(); own_raft_phys cfg r id (send_msgs s out) }}}.

Module Type SEND.
  Parameter wp_raft__send : wp_raft__send_body.
  Arguments wp_raft__send {_ _ _ _ _ _ _ _}.
End SEND.
