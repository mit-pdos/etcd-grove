Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.step_lemmas.

(** * [stepCandidate], for the message types in scope

    [stepCandidateⁱᵐᵖˡ] (new/code/go_etcd_io/raft/v3.v:4618;
    raft.go:1660) first reads [r.state] to pick [myVoteRespType]
    ([MsgVoteResp] for a candidate), then switches on [m.Type]:

    - [MsgProp]: [Infof], [return ErrProposalDropped]; state unchanged.
    - [MsgApp]: [becomeFollower(m.Term, m.From)] -- "always [m.Term ==
      r.Term]", which is a premise here -- then [handleAppendEntries].
    - [MsgVoteResp]: record the vote, then win, lose or keep waiting.
    - [MsgHeartbeat]: [becomeFollower(m.Term, m.From)] -- again "always
      [m.Term == r.Term]", a premise -- then [handleHeartbeat]
      ([heartbeat_result] at the follower state).
    - [MsgBeat], [MsgAppResp], [MsgHeartbeatResp]: no arm (they are none of
      the above, nor [MsgSnap], [myVoteRespType] or [MsgTimeoutNow]);
      nothing written, [nil].

    Ghost-free.  It used to take [own_raft_ghost] and [is_message] for the
    incoming message, but that was only ever feeding [own_raft_ghost_step];
    [is_message] is what justifies *the model transition*, not the code, so
    it belongs at the one place the transition is taken — [Step].  (Until
    2026-10-01 this collection was [stepCandidate_MsgVoteResp], stated for
    [MsgVoteResp] only; that case's postcondition is unchanged.) *)

Section results.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

(** The [MsgVoteResp] case, as it was.

    The quorum facts are **part of the spec**, not incidental.  Without
    them this triple is true but useless to its caller: [Step]'s
    [MsgVoteResp] branch has to justify the resulting [role.Leader] by
    [step_win], whose premise is [is_quorum cfg (granted …)], and no other
    [step] rule produces a leader.  [poll] establishes both facts; before
    2026-09-16 the proof dropped them on the floor and [won]/[lost]
    escaped as unconstrained booleans.  [ms] is what [bcastAppend]
    broadcast on a win: what [repl_sends] allows, possibly nothing.
    [record_vote] does not touch the term, so [s1]'s term is [s]'s. *)
Definition cand_vote_resp_result (cfg : gset w64) (id : w64)
    (s : nstate.t) (m : raftpb.Message.t) (s' : nstate.t) : Prop :=
  ∃ won lost ms pvs,
    let votes' := record_vote s.(nstate.votes)
                    m.(raftpb.Message.From')
                    (negb m.(raftpb.Message.Reject')) in
    (won = true →
       is_quorum cfg (granted votes') ∧
       (* the broadcast, judged at the new leader's state *)
       repl_sends id (become_leader id (s <| nstate.votes := votes' |>)) ms ∧
       (* [Match] is what [becomeLeader]'s [reset] left *)
       prvals_match pvs = reset_matched id (log_last s.(nstate.logst)) s.(nstate.prvals)) ∧
    (lost = true → ¬ is_quorum cfg (cfg ∖ rejected votes')) ∧
    s' = vote_resp_result id s m.(raftpb.Message.From')
           m.(raftpb.Message.Reject') won lost ms <| nstate.prvals := pvs |>.

(** What [stepCandidate] does with [m], by type; [dropped] as in
    [follower_step_result] ([spec_stepFollower.v]).  For [MsgApp] the
    [Progress] values [becomeFollower]'s [reset] leaves are [pvs]
    (unconstrained: a follower's are invisible to [to_pstate]). *)
Definition candidate_step_result (cfg : gset w64) (id : w64)
    (s : nstate.t) (m : raftpb.Message.t) (ents : list raftpb.Entry.t)
    (dropped : bool) (s' : nstate.t) : Prop :=
  if decide (m.(raftpb.Message.Type') = MsgVoteResp) then dropped = false ∧ cand_vote_resp_result cfg id s m s'
  else if decide (m.(raftpb.Message.Type') = MsgProp) then dropped = true ∧ s' = s
  else if decide (m.(raftpb.Message.Type') = MsgApp) then
    dropped = false ∧
    ∃ pvs, handle_app_result id
             (become_follower s s.(nstate.term) m.(raftpb.Message.From')
                <| nstate.prvals := pvs |>) m ents s'
  else if decide (m.(raftpb.Message.Type') = MsgHeartbeat) then
    dropped = false ∧
    ∃ pvs, s' = heartbeat_result id
                  (become_follower s s.(nstate.term) m.(raftpb.Message.From')
                     <| nstate.prvals := pvs |>) m
  else if decide (m.(raftpb.Message.Type') = MsgBeat ∨
                  m.(raftpb.Message.Type') = MsgAppResp ∨
                  m.(raftpb.Message.Type') = MsgHeartbeatResp) then
    dropped = false ∧ s' = s
  else False.

End results.

(** Premises:
    - [s.role = Candidate]: [myVoteRespType] is then [MsgVoteResp] (and
      not [MsgPreVoteResp]); [r.step = stepCandidate] means it
      ([nstate_wf]);
    - [m.Term = r.Term] for [MsgVoteResp], [MsgApp] and [MsgHeartbeat]
      ([Step]'s term preamble has run; for the last two it is the Go
      comment's "always [m.Term == r.Term]");
    - [id ∈ cfg]: a candidate that can win is a voter; [poll] needs [cfg]
      non-empty and [becomeLeader] needs this outright, and neither is
      available from [own_raft_phys], so it is threaded in from the caller;
    - [MsgApp]: [handleAppendEntries]'s premises, at [s] ([becomeFollower]
      leaves the log alone);
    - [MsgHeartbeat]: [handleHeartbeat]'s premises, at [s] (likewise):
      [m.Commit] within the log and [m.From ≠ id];
    - [Hents]: the [Entries] slice and its capacity, for [MsgApp] only. *)
Definition wp_stepCandidate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t),
  (m.(raftpb.Message.Type') = MsgVoteResp ∨ m.(raftpb.Message.Type') = MsgProp ∨
   m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgHeartbeat ∨
   m.(raftpb.Message.Type') = MsgBeat ∨ m.(raftpb.Message.Type') = MsgAppResp ∨
   m.(raftpb.Message.Type') = MsgHeartbeatResp) →
  (m.(raftpb.Message.Type') = MsgVoteResp ∨ m.(raftpb.Message.Type') = MsgApp ∨
   m.(raftpb.Message.Type') = MsgHeartbeat →
   m.(raftpb.Message.Term') = s.(nstate.term)) →
  s.(nstate.role) = role.Candidate →
  id ∈ cfg →
  (m.(raftpb.Message.Type') = MsgApp →
     plog_wf (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) ents ∧
     (uint.Z m.(raftpb.Message.Index') + Z.of_nat (length ents) + 1 < 2^64)%Z ∧
     Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents ∧
     (let ls := s.(nstate.logst) in
      let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
      uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') →
      plog_matches ls.(logstate.prev) es
        (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
      plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
      uint.Z ls.(logstate.committed) < uint.Z (plog_find_conflict ls.(logstate.prev) es ents))%Z) →
  (m.(raftpb.Message.Type') = MsgHeartbeat →
     (uint.Z m.(raftpb.Message.Commit')
        ≤ plog_last_index_Z s.(nstate.logst).(logstate.prev)
            (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents)))%Z ∧
     m.(raftpb.Message.From') ≠ id) →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hents" ∷ (⌜ m.(raftpb.Message.Type') = MsgApp ⌝ -∗
                 m.(raftpb.Message.Entries') ↦*□ ents ∗
                 own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1)) }}}
    @! raft.stepCandidate #r #m
  {{{ (err : error.t) (s' : nstate.t) (dropped : bool), RET #err;
      own_raft_phys cfg r id s' ∗
      ⌜ candidate_step_result cfg id s m ents dropped s' ⌝ ∗
      (if dropped then (global_addr raft.ErrProposalDropped) ↦□ err
       else ⌜ err = interface.nil ⌝) }}}.

Module Type STEPCANDIDATE.
  Parameter wp_stepCandidate : wp_stepCandidate_body.
  Arguments wp_stepCandidate {_ _ _ _ _ _ _ _}.
End STEPCANDIDATE.
