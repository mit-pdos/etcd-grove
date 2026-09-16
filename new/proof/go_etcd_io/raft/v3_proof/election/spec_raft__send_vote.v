Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [send] is the only place a message reaches the network, so this is where
    the abstract outbox grows.  It stamps the sender's id into [From], and
    routes vote *responses* to [msgsAfterAppend] and everything else to
    [msgs]; the model has a single outbox, so that routing is invisible here.

    Note there is no [is_message] precondition any more.  [send] does not have
    to know the message is protocol-legal — it only records that the node put
    it in its outbox.  Legality is established once, by [Step], against
    [own_raft_ghost]. *)
Definition wp_raft__send_vote_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t) (ty : mtype.t),
  m.(raftpb.Message.From') = W64 0 →
  m.(raftpb.Message.Type') = MsgVote ∨ m.(raftpb.Message.Type') = MsgVoteResp →
  mtype_of m.(raftpb.Message.Type') = Some ty →
  m.(raftpb.Message.Term') ≠ W64 0 →
  (* [send] panics on a self-addressed non-response; a candidate never sends
     itself a [MsgVote]. *)
  (m.(raftpb.Message.Type') = MsgVote → m.(raftpb.Message.To') ≠ id) →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "send" #m
  {{{ RET #();
      own_raft_phys cfg r id
        (send_msgs s [msg.mk ty id m.(raftpb.Message.To')
                        m.(raftpb.Message.Term') m.(raftpb.Message.Reject')]) }}}.

Module Type SEND_VOTE.
  Parameter wp_raft__send_vote : wp_raft__send_vote_body.
  Arguments wp_raft__send_vote {_ _ _ _ _ _ _ _}.
End SEND_VOTE.
