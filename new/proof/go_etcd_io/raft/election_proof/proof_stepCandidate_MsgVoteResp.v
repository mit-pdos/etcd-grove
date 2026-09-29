Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepCandidate_MsgVoteResp.

Module StepCandidateProof (P : STEPCANDIDATE_POSTULATES) : STEPCANDIDATE.
Import P.

  (** [stepCandidate] on a [MsgVoteResp].  The type switch is walked to the
      [myVoteRespType] arm ([m.Type = MsgVoteResp], and [state = StateCandidate]
      so [myVoteRespType] is [MsgVoteResp] and not [MsgPreVoteResp]), then
      [poll] records the vote and the [res] switch does one of three things:
      win and broadcast, lose and step down, or nothing.

      Each arm lands on [vote_resp_result] directly.  [VoteWon] is
      [becomeLeader] followed by [bcastAppend], whose spec gives *some* list of
      [App]s from [id] at the current term rather than one per peer -- which is
      exactly what the weakened [step_win]/[app_sends] asks for, so no
      massaging is needed.  [VoteLost] is [becomeFollower(r.Term, None)], and
      [become_follower s1 s1.(nstate.term) (W64 0)] is verbatim
      [vote_resp_result]'s [lost] branch.  [VotePending] leaves the state at
      [s1] and sends nothing. *)
  Lemma wp_stepCandidate_MsgVoteResp : wp_stepCandidate_MsgVoteResp_body.
  Proof.
    intros_ambient.
    intros cfg r id s m.
    intros Hty Hto Hterm Hrole Hcfg Hlent.
    wp_start as "Hphys". wp_auto. wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
    (* [state = StateCandidate ≠ StatePreCandidate], so [myVoteRespType] is
       [MsgVoteResp]. *)
    rewrite Hrole /state_w64 /StateCandidate.
    rewrite bool_decide_eq_false_2; last w32_ne.
    wp_auto.
    (* the type switch: [MsgVoteResp] is none of [MsgProp], [MsgApp],
       [MsgHeartbeat], [MsgSnap], so it falls through to [myVoteRespType].
       Only the first comparison needs help; once [m.Type] is the literal
       [W32 6], [wp_auto] decides the rest by computation. *)
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
    assert (cfg ≠ ∅) as Hcfg_ne by set_solver.
    wp_apply (P.wp_raft__poll _ _ _ _ _ _ _ Hlent Hcfg_ne with "[$Hphys]")
      as "%g %rj0 %res (Hphys & %Hres & %Hwon & %Hlost)".
    (* the [Infof] that follows reads [r.id], [r.Term] and [r.logger] *)
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
    set (s1 := s <| nstate.votes :=
                 record_vote s.(nstate.votes) m.(raftpb.Message.From')
                   (negb m.(raftpb.Message.Reject')) |>).
    destruct Hres as [Hres|[Hres|Hres]]; rewrite Hres.
    - (* [quorum.VoteWon]: become leader and broadcast. *)
      rewrite /VoteWon bool_decide_eq_true_2 //. wp_auto.
      (* [poll] does not touch the role, so we are still a candidate: not a
         pre-candidate, so this is [becomeLeader] and not [campaign]. *)
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      assert (s1.(nstate.role) = role.Candidate) as Hrole1 by exact Hrole.
      rewrite Hrole1 /state_w64 /StateCandidate bool_decide_eq_false_2; last w32_ne.
      wp_auto.
      wp_apply (P.wp_raft__becomeLeader with "[$Hphys]").
      { rewrite Hrole1. congruence. }
      { done. }
      { exact Hlent. }
      iIntros "Hphys". wp_auto.
      (* [bcastAppend] adds *some* list of [App]s from [id] at the current
         term -- not one per peer; see [spec_raft__bcastAppend.v]. *)
      wp_apply (wp_raft__bcastAppend with "[$Hphys]"); first exact Hlent.
      iIntros (ms) "[Hphys %Hms]". try wp_auto.
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      (* The postcondition is [⌜∃ …⌝ ∗ ⌜err = nil⌝]; [iFrame "Hphys"] does
         *not* discharge the second, so [iPureIntro] leaves a conjunction. *)
      iPureIntro. split; last done. exists true, false, ms. simpl in Hms.
      split_and!;
        [ exact Hms
        | intros _; by apply Hwon
        | intros [=]
        | rewrite /vote_resp_result // ].
    - (* [quorum.VoteLost]: step down at the unchanged term. *)
      rewrite /VoteLost bool_decide_eq_false_2; last w32_ne. wp_auto.
      (* the [r.Term] the code passes is [s1]'s term *)
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      wp_apply (P.wp_raft__becomeFollower with "[$Hphys]"); first exact Hlent.
      iIntros "Hphys". try wp_auto.
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; last done. exists false, true, [].
      split_and!;
        [ rewrite /app_sends; constructor
        | intros [=]
        | intros _; by apply Hlost
        | rewrite /vote_resp_result // ].
    - (* [quorum.VotePending]: neither switch arm fires; keep waiting. *)
      rewrite /VotePending bool_decide_eq_false_2; last w32_ne. wp_auto.
      iApply ("HΦ" $! interface.nil s1). iFrame "Hphys".
      iPureIntro. split; last done. exists false, false, [].
      split_and!;
        [ rewrite /app_sends; constructor
        | intros [=]
        | intros [=]
        | rewrite /vote_resp_result // ].
  Qed.

End StepCandidateProof.
