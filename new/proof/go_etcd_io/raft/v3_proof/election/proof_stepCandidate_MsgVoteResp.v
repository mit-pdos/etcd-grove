Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepCandidate_MsgVoteResp.

Module StepCandidateProof (P : STEPCANDIDATE_POSTULATES) : STEPCANDIDATE.

  Lemma wp_stepCandidate_MsgVoteResp : wp_stepCandidate_MsgVoteResp_body.
  Proof.
    intros_ambient.
    intros cfg r id s m.
    intros Hty Hto Hterm Hrole Hcfg.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [state = StateCandidate ≠ StatePreCandidate], so [myVoteRespType] is
       [MsgVoteResp]. *)
    rewrite Hstate Hrole /state_w64 /StateCandidate.
    rewrite bool_decide_eq_false_2; last w32_ne.
    wp_auto.
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
    (* re-seal for the [poll] call *)
    iAssert (own_raft_phys cfg r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
    wp_apply (P.wp_raft__poll with "[$Hphys]")
      as "%g %rj0 %res (Hphys & %Hres & %Hwon & %Hlost)".
    iNamedSuffix "Hphys" "1".
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    destruct Hres as [Hres|[Hres|Hres]]; rewrite Hres.
    - (* [quorum.VoteWon] *)
      rewrite /VoteWon bool_decide_eq_true_2 //. wp_auto.
      (* [poll] does not touch the role, so we are still a candidate: not a
         pre-candidate, so this is [becomeLeader] and not [campaign]. *)
      assert (rv0.(raft.raft.state') = StateCandidate) as Hstc.
      { rewrite Hstate1 /= Hrole //. }
      rewrite Hstc /StateCandidate bool_decide_eq_false_2; last w32_ne.
      wp_auto.
      iAssert (own_raft_phys cfg r id
                 (s <| nstate.votes :=
                    record_vote s.(nstate.votes) m.(raftpb.Message.From')
                      (negb m.(raftpb.Message.Reject')) |>))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
        iFrame "∗#%". }
      wp_apply (P.wp_raft__becomeLeader with "[$Hphys]").
      { rewrite /= Hrole. congruence. }
      { done. }
      iIntros "Hphys". wp_auto.
      (* [bcastAppend] adds some list of [App]s from [id] at the current
         term -- not one per peer; see the lemma's comment. *)
      wp_apply (wp_raft__bcastAppend with "[$Hphys]") as "%ms [Hphys %Hms]".
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. exists true, false, ms.
      simpl in Hms. split; first done. rewrite /vote_resp_result //.
    - rewrite /VoteLost bool_decide_eq_false_2; last w32_ne. wp_auto.
      Show.
      admit.
    - (* [quorum.VotePending]: neither switch arm fires; keep waiting. *)
      rewrite /VotePending bool_decide_eq_false_2; last w32_ne. wp_auto.
      iApply ("HΦ" $! interface.nil
                (s <| nstate.votes :=
                   record_vote s.(nstate.votes) m.(raftpb.Message.From')
                     (negb m.(raftpb.Message.Reject')) |>)).
      iSplitL "Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1".
      { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
        iFrame "∗#%". }
      iPureIntro. exists false, false, []. split.
      { rewrite /app_sends. constructor. }
      rewrite /vote_resp_result //.
  Admitted.

End StepCandidateProof.
