Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.handleHeartbeat(m)] ([raft__handleHeartbeatⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:4949; [raft.go:1822]):

      r.raftLog.commitTo(m.Commit)
      r.send(pb.Message{To: m.From, Type: pb.MsgHeartbeatResp, Context: m.Context})

    Two exits that are not [return]: [commitTo] [Panicf]s when
    [m.Commit > lastIndex()], and [send] [Panicf]s on a self-addressed
    [MsgHeartbeatResp] (it goes onto [r.msgs]).  Each is ruled out by a
    premise: the first is the protocol fact [heartbeat_commit_le_last]
    ([protocol.v]) that [Step] supplies, stated on the log as [own_raft_phys]
    records it; the second is that the sender is not this node.

    The postcondition is the follower's half of [step_heartbeat]:
    [committed] becomes [plog_commit_to committed m.Commit] (it never moves
    back) and the outbox grows by exactly the [HeartbeatResp] the model's
    rule names, [msg.plain mtype.HeartbeatResp id m.From s.term false].
    That is what [send_ok]'s clause (b) makes of the literal: [send] stamps
    [From := r.id] and [Term := r.Term]; the literal sets only
    [To]/[Type]/[Context], so [Reject] is [false], [Index]/[LogTerm]/
    [Commit]/[RejectHint] are [0], and [Entries] is the nil slice, whose
    list is [[]].  ([Context] is not part of the abstraction.)  Adopting the
    leader ([lead := m.From], [becomeFollower]) is the caller's business
    ([stepFollower]/[stepCandidate]); this function does not do it. *)
Definition wp_raft__handleHeartbeat_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  (uint.Z m.(raftpb.Message.Commit')
     ≤ plog_last_index_Z s.(nstate.logst).(logstate.prev)
         (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents)))%Z →
  m.(raftpb.Message.From') ≠ id →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "handleHeartbeat" #m
  {{{ RET #();
      own_raft_phys cfg r id
        (send_msgs
           (s <| nstate.logst :=
                  s.(nstate.logst) <| logstate.committed :=
                    plog_commit_to s.(nstate.logst).(logstate.committed)
                      m.(raftpb.Message.Commit') |> |>)
           [msg.plain mtype.HeartbeatResp id m.(raftpb.Message.From')
              s.(nstate.term) false]) }}}.

Module Type RAFT__HANDLEHEARTBEAT.
  Parameter wp_raft__handleHeartbeat : wp_raft__handleHeartbeat_body.
  Arguments wp_raft__handleHeartbeat {_ _ _ _ _ _ _ _}.
End RAFT__HANDLEHEARTBEAT.
