Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepCandidate_MsgVoteResp.

Module StepCandidateProof (P : STEPCANDIDATE_POSTULATES) : STEPCANDIDATE.

  (** [stepCandidate] on a [MsgVoteResp].  The type switch is walked to the
      [myVoteRespType] arm ([m.Type = MsgVoteResp], and [state = StateCandidate]
      so [myVoteRespType] is [MsgVoteResp] and not [MsgPreVoteResp]), then
      [poll] records the vote and the [res] switch does one of three things.

      **Unfinished: the [quorum.VoteLost] arm.**  It is
      [r.becomeFollower(r.Term, None)], and [P] does not offer
      [wp_raft__becomeFollower]: [STEPCANDIDATE_POSTULATES] is
      [POLL + BECOMELEADER + SEND_VOTE].  That list is wrong in both
      directions -- [SEND_VOTE] is never used on this path, and
      [BECOMEFOLLOWER] is needed.  Fixing it is a change to
      [postulates_stepCandidate_MsgVoteResp.v] (add
      [Include BECOMEFOLLOWER.]) and [link_stepCandidate_MsgVoteResp.v] (add
      [Include BecomeFollower.], and the [Require Export] of
      [link_raft__becomeFollower]), which are shared files this proof may not
      touch.  Note [postulates_raft__Step.v] already includes both
      [BECOMEFOLLOWER] and [STEPCANDIDATE], so nothing above breaks.

      With that in place the arm is the five lines below the [wp_auto] that
      ends this proof:

        iAssert (own_raft_phys cfg r id
                   (s <| nstate.votes :=
                      record_vote s.(nstate.votes) m.(raftpb.Message.From')
                        (negb m.(raftpb.Message.Reject')) |>))
          with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
          as "Hphys".
        { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
          iFrame "∗#%". }
        rewrite Hterm1.
        wp_apply (P.wp_raft__becomeFollower with "[$Hphys]") as "Hphys".
        iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
        iPureIntro. exists false, true, []. split.
        { rewrite /app_sends. constructor. }
        rewrite /vote_resp_result //.

      ([become_follower s1 s1.(nstate.term) (W64 0)] is literally
      [vote_resp_result]'s [lost] branch, and [r.Term = s1.(nstate.term)] is
      [Hterm1].) *)
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
    (* the type switch: [MsgVoteResp] is none of [MsgProp], [MsgApp],
       [MsgHeartbeat], [MsgSnap], so it falls through to [myVoteRespType].
       Only the first comparison needs help; once [m.Type] is the literal
       [W32 6], [wp_auto] decides the rest by computation. *)
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
    (* re-seal for the [poll] call *)
    iAssert (own_raft_phys cfg r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
    wp_apply (P.wp_raft__poll with "[$Hphys]")
      as "%g %rj0 %res (Hphys & %Hres & %Hwon & %Hlost)".
    (* unpack again: the [Infof] that follows reads [r.id] and [r.logger] *)
    iNamedSuffix "Hphys" "1".
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    (* the [res] switch.  [VoteWon] and [VotePending] are done here; the
       [VoteLost] arm is left as the single [Admitted] -- see above. *)
    destruct Hres as [Hres|[Hres|Hres]]; rewrite Hres.
    (* [quorum.VoteWon]: become leader and broadcast. *)
    1:{
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
      (* [bcastAppend] adds *some* list of [App]s from [id] at the current
         term -- not one per peer; see the lemma's comment in
         [inv_raft_phys.v]. *)
      wp_apply (wp_raft__bcastAppend with "[$Hphys]") as "%ms [Hphys %Hms]".
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. exists true, false, ms.
      simpl in Hms. split; first done. rewrite /vote_resp_result //.
    }
    (* [quorum.VotePending]: neither switch arm fires; keep waiting.  (This
       is goal 2 once the [VoteWon] goal above is closed.) *)
    2:{
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
    }
    (* [quorum.VoteLost]: step down.  Stepped up to the [becomeFollower]
       call; the call itself needs [BECOMEFOLLOWER] in
       [STEPCANDIDATE_POSTULATES].  See the comment on this lemma. *)
    rewrite /VoteLost bool_decide_eq_false_2; last w32_ne. wp_auto.
  Admitted.

End StepCandidateProof.
