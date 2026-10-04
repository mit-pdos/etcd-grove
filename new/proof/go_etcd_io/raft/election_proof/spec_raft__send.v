Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

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
    ([abs_msg_from] of the stamped message), given case by case by
    [send_ok] below.  There is no [is_message] precondition: [send] does not
    have to know the message is protocol-legal, it only records that the node
    put it in its outbox.  Legality is established once, by [Step], against
    [own_raft_ghost]. *)

(** [send_ok id s m ents out]: the message [m], whose [Entries] slice holds
    [ents], takes a non-panicking path through [send] on a node with id [id]
    in state [s], and [out] is what the abstract outbox grows by -- the
    abstraction of the message as queued, i.e. of [m] with [From := id] and
    [Term] as [send] leaves it ([abs_msg_from], [defs.v]).  One clause per
    shape a caller builds:

    (a) a vote request/response ([MsgVote], [MsgVoteResp], and since
        2026-10-04 [MsgPreVote], [MsgPreVoteResp]).  [Term] is the
        caller's and is kept.  A request goes onto [r.msgs] and must not
        be self-addressed; a response may be.
    (b) a message stamped with the current term and queued on [r.msgs]:
        [MsgApp], [MsgHeartbeat], [MsgReadIndexResp], [MsgHeartbeatResp].
        [Term] must be unset; the abstract message carries [s.term], which
        is what [send] stamps in ([r.Term = s.term] by [own_raft_phys]).
        Not self-addressed ([Panicf]).  ([MsgSnap] was here until
        2026-10-02; it has its own clause now, (c').  [MsgReadIndexResp],
        which nothing in scope sends, takes exactly this path through the
        body and holds its place, so that a caller's [by right; right;
        right] still picks [MsgHeartbeatResp].)
    (c) a message the model does not describe ([mtype_of = None]).  It is
        queued and drops out of the abstract outbox.  [Term] unset, not
        self-addressed.
    (c') [MsgSnap] (2026-10-02): stamped and queued like (b), but the
        abstract message is [abs_snap_from] of the snapshot [m.Snapshot]
        points to and of that snapshot's [ConfState.Voters].  [send] does
        not read the pointer, so the caller names the two and supplies
        their read-only points-tos: the precondition's ["Hsnap"] fixes
        [out = [abs_snap_from m id s.term sv voters]] for exactly those
        [sv]/[voters] (since 2026-10-03; until then the clause itself
        said [∃ sv voters, out = ...], untied to the heap).  (Stated as
        the left disjunct of (c), which no caller uses, so that no
        caller's clause selection moved.)
    (d) [MsgAppResp]: stamped like (b), but a response, so it goes onto
        [r.msgsAfterAppend] and may be self-addressed ([appendEntry]'s
        self-acknowledgement is).
    (e) [MsgProp], forwarded to the leader: [Term] must be unset and stays
        [0] (the body's [MsgProp]/[MsgReadIndex] exception); onto [r.msgs],
        not self-addressed.

    The read-index types are in no clause: nothing in scope sends them (no
    read requests).
    Until 2026-10-01 [MsgAppResp], [MsgSnap] and [MsgHeartbeatResp] were
    under (c), invisible to the model. *)
Definition send_ok {ext : ffi_syntax} (id : w64) (s : nstate.t) (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t) (out : list msg.t) : Prop :=
  (∃ ty,
     (m.(raftpb.Message.Type') = MsgVote ∨ m.(raftpb.Message.Type') = MsgVoteResp ∨
      m.(raftpb.Message.Type') = MsgPreVote ∨ m.(raftpb.Message.Type') = MsgPreVoteResp) ∧
     mtype_of m.(raftpb.Message.Type') = Some ty ∧
     m.(raftpb.Message.Term') ≠ W64 0 ∧
     (m.(raftpb.Message.Type') = MsgVote ∨ m.(raftpb.Message.Type') = MsgPreVote →
      m.(raftpb.Message.To') ≠ id) ∧
     out = [abs_msg_from ty m id m.(raftpb.Message.Term') ents])
  ∨
  (∃ ty,
     (m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgHeartbeat ∨
      m.(raftpb.Message.Type') = MsgReadIndexResp ∨
      m.(raftpb.Message.Type') = MsgHeartbeatResp) ∧
     mtype_of m.(raftpb.Message.Type') = Some ty ∧
     m.(raftpb.Message.Term') = W64 0 ∧
     m.(raftpb.Message.To') ≠ id ∧
     out = [abs_msg_from ty m id s.(nstate.term) ents])
  ∨
  ((m.(raftpb.Message.Type') = MsgSnap ∧
    m.(raftpb.Message.Term') = W64 0 ∧
    m.(raftpb.Message.To') ≠ id)
   ∨
   (mtype_of m.(raftpb.Message.Type') = None ∧
    m.(raftpb.Message.Term') = W64 0 ∧
    m.(raftpb.Message.To') ≠ id ∧
    out = []))
  ∨
  (m.(raftpb.Message.Type') = MsgAppResp ∧
   m.(raftpb.Message.Term') = W64 0 ∧
   out = [abs_msg_from mtype.AppResp m id s.(nstate.term) ents])
  ∨
  (m.(raftpb.Message.Type') = MsgProp ∧
   m.(raftpb.Message.Term') = W64 0 ∧
   m.(raftpb.Message.To') ≠ id ∧
   out = [abs_msg_from mtype.Propose m id (W64 0) ents]).

(** A caller discharges [send_ok] by picking the clause and splitting it:
    for a vote message with [ty] the abstract type,

      left; exists ty; split_and!;
        [by right; left | apply mtype_of_MsgVoteResp | <Term ≠ 0>
         | intros [Hc|Hc]; revert Hc; w32_ne | done]

    (the fourth discharges the request clause for a response type)

    (the last [done] fixes [out]); for a [MsgApp], [right; left; exists
    mtype.App; split_and!; [by left | .. | done | <To ≠ id> | done]]; for
    [MsgAppResp], [right; right; right; left; split_and!; [done | done |
    done]]; for [MsgSnap], [right; right; left; left; split_and!; [done |
    done | <To ≠ id>]].  These are not lemmas here because a spec file
    states and does not prove (etc/check-module-discipline.py, F3).

    **[ents].**  [m.Entries ↦*□ ents] is a precondition: it is what
    [own_raft_phys] keeps for the queued message ([outbox_rel],
    [inv_raft_phys.v]).  For a message built without [Entries] the field
    is [slice.nil] and [ents = []] ([own_slice_nil]).

    **["Hsnap"]** (2026-10-03): for a [MsgSnap], the snapshot [sv] that
    [m.Snapshot] points to and its [ConfState.Voters] list [voters], both
    read-only, and [out] is the abstraction at those -- what
    [own_raft_phys] keeps for the queued message ([msg_abs]).  Every other
    caller discharges it from its message type ([send_no_snap],
    [inv_raft_phys.v]). *)

(** Stated on [own_raft_phys], for **any** [s].  [send] touches [r.msgs],
    [r.msgsAfterAppend], [r.logger] and the tracing hook, and *reads*
    [r.id] and [r.Term]; everything else in [s] -- the tracker's progress
    map and [Progress] values, the log -- comes back as it went in, because
    [send_msgs] changes only the outbox.  [maybeSendAppend] relies on it:
    it reads a [Progress] before this call and needs it unchanged after
    ([nstate.prvals]), and holds [ents] (read-only) across it.

    From 2026-09-21 to 2026-09-22 this was stated on a variant predicate,
    [own_raft_bare]; see notes/decisions.md ("Three layers") and
    notes/false-statements.md, 2026-09-21. *)
Definition wp_raft__send_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (m : raftpb.Message.t) (ents : list raftpb.Entry.t) (out : list msg.t),
  m.(raftpb.Message.From') = W64 0 →
  send_ok id s m ents out →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
      "#Hsnap" ∷ □ (⌜ m.(raftpb.Message.Type') = MsgSnap ⌝ -∗
                    ∃ (sv : raftpb.Snapshot.t) (voters : list w64),
                      ⌜ out = [abs_snap_from m id s.(nstate.term) sv voters] ⌝ ∗
                      m.(raftpb.Message.Snapshot') ↦□ sv ∗
                      sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                        .(raftpb.ConfState.Voters') ↦*□ voters) }}}
    r @! (go.PointerType raft.raft) @! "send" #m
  {{{ RET #(); own_raft_phys cfg r id (send_msgs s out) }}}.

Module Type SEND.
  Parameter wp_raft__send : wp_raft__send_body.
  Arguments wp_raft__send {_ _ _ _ _ _ _ _}.
End SEND.
