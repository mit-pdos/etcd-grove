Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.step_lemmas.

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
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    @! raft.stepCandidate #r #m
  {{{ (err : error.t) s', RET #err;
      own_raft_phys cfg r id s' ∗
      (* [ms] is what [bcastAppend] broadcast on a win: some list of [App]s
         from [id] at the current term, possibly empty.  [record_vote] does
         not touch the term, so this is [s]'s term. *)
      (* The quorum facts are **part of the spec**, not incidental.  Without
         them this triple is true but useless to its caller: [Step]'s
         [MsgVoteResp] branch has to justify the resulting [role.Leader] by
         [step_win], whose premise is [is_quorum cfg (granted …)], and no
         other [step] rule produces a leader.  [poll] establishes both facts
         and [proof_stepCandidate_MsgVoteResp.v] receives them as
         [%Hwon]/[%Hlost]; before 2026-09-16 it dropped them on the floor and
         [won]/[lost] escaped here as unconstrained booleans.

         [record_vote] does not touch the term, so [s1]'s term is [s]'s. *)
      ⌜ ∃ won lost ms,
          let votes' := record_vote s.(nstate.votes)
                          m.(raftpb.Message.From')
                          (negb m.(raftpb.Message.Reject')) in
          app_sends id s.(nstate.term) ms ∧
          (won = true → is_quorum cfg (granted votes')) ∧
          (lost = true → ¬ is_quorum cfg (cfg ∖ rejected votes')) ∧
          s' = vote_resp_result id s m.(raftpb.Message.From')
                 m.(raftpb.Message.Reject') won lost ms ⌝ ∗
      (* The [MsgVoteResp] arm of [stepCandidate]'s type switch ends in
         [return nil].  [Step] needs this written down: its own postcondition
         claims a [nil] error, and the code propagates a non-nil one out of
         [r.step(m)] unchanged. *)
      ⌜ err = interface.nil ⌝ }}}.

Module Type STEPCANDIDATE.
  Parameter wp_stepCandidate_MsgVoteResp : wp_stepCandidate_MsgVoteResp_body.
  Arguments wp_stepCandidate_MsgVoteResp {_ _ _ _ _ _ _ _}.
End STEPCANDIDATE.
