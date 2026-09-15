Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.step_lemmas.

(** [stepCandidate] on a [MsgVoteResp]: record the vote, then win, lose or
    keep waiting.

    Ghost-free.  It used to take [own_raft_ghost] and [is_message] for the
    incoming message, but that was only ever feeding [own_raft_ghost_step];
    [is_message] is what justifies *the model transition*, not the code, so it
    belongs at the one place the transition is taken — [Step]. *)
Definition wp_stepCandidate_MsgVoteResp_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgVoteResp →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  (* A candidate that can win an election is a voter.  [poll] needs [cfg] in
     scope and [becomeLeader] needs this premise outright; neither is
     available from [own_raft_phys], so it is threaded in from the caller. *)
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ own_raft_phys r id s }}}
    @! raft.stepCandidate #r #m
  {{{ (err : error.t) s', RET #err;
      own_raft_phys r id s' ∗
      ⌜ ∃ won lost peers,
          peers ≡ₚ elements (cfg ∖ {[id]}) ∧
          s' = vote_resp_result id s m.(raftpb.Message.From')
                 m.(raftpb.Message.Reject') won lost peers ⌝ }}}.

Module Type STEPCANDIDATE.
  Parameter wp_stepCandidate_MsgVoteResp : wp_stepCandidate_MsgVoteResp_body.
  Arguments wp_stepCandidate_MsgVoteResp {_ _ _ _ _ _ _ _}.
End STEPCANDIDATE.
