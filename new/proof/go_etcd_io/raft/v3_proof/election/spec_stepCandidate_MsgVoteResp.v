Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.step_lemmas.

(** [stepCandidate] on a [MsgVoteResp]: record the vote, then win, lose or
    keep waiting. *)
Definition wp_stepCandidate_MsgVoteResp_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgVoteResp →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  (* A candidate that can win an election is a voter.  [poll] needs [cfg] in
     scope and [becomeLeader] needs this premise outright; neither is
     available from [own_raft_phys], so it is threaded in from the caller. *)
  id ∈ cfg →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.VoteResp m)
  }}}
    @! raft.stepCandidate #r #m
  {{{ (err : error.t) s', RET #err;
      own_raft_phys γ r id s' ∗ own_raft_ghost γ id s' ∗
      ⌜ ∃ won lost,
          s' = vote_resp_result id s m.(raftpb.Message.From')
                 m.(raftpb.Message.Reject') won lost ⌝ }}}.

Module Type STEPCANDIDATE.
  Parameter wp_stepCandidate_MsgVoteResp : wp_stepCandidate_MsgVoteResp_body.
End STEPCANDIDATE.
