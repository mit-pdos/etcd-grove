(** * Spec: [raft.raft__send_vote]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] is a bare reference to
    it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [send] is the only place a message reaches the network, so this is where
    the [is_message] obligation is discharged: the caller must already know
    the abstract message is legal. *)
Definition wp_raft__send_vote_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t) (ty : mtype.t),
  m.(raftpb.Message.From') = W64 0 →
  m.(raftpb.Message.Type') = MsgVote ∨ m.(raftpb.Message.Type') = MsgVoteResp →
  mtype_of m.(raftpb.Message.Type') = Some ty →
  m.(raftpb.Message.Term') ≠ W64 0 →
  (* [send] panics on a self-addressed non-response; a candidate never sends
     itself a [MsgVote]. *)
  (m.(raftpb.Message.Type') = MsgVote → m.(raftpb.Message.To') ≠ id) →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "#Hm" ∷ is_message γ (msg.mk ty id m.(raftpb.Message.To')
                              m.(raftpb.Message.Term') m.(raftpb.Message.Reject'))
  }}}
    r @! (go.PointerType raft.raft) @! "send" #m
  {{{ RET #(); own_raft_phys γ r id s }}}.

Module Type SEND_VOTE.
  Parameter wp_raft__send_vote : wp_raft__send_vote_body.
End SEND_VOTE.
