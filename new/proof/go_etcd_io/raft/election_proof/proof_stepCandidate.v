Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepCandidate.

Module StepCandidateProof (P : STEPCANDIDATE_POSTULATES) : STEPCANDIDATE.
Import P.

  (** By type.  [MsgProp]: [Infof], then [return ErrProposalDropped] (the
      global's points-to from [is_pkg_init_access]).  [MsgApp]:
      [becomeFollower(m.Term, m.From)] with [m.Term = s.term], then
      [handleAppendEntries] at the follower state.  [MsgHeartbeat]: the
      same [becomeFollower], then [handleHeartbeat].  [MsgBeat],
      [MsgAppResp], [MsgHeartbeatResp]: no arm.

      [MsgVoteResp], unchanged since 2026-09: the type switch is walked to the
      [myVoteRespType] arm ([m.Type = MsgVoteResp], and [state = StateCandidate]
      so [myVoteRespType] is [MsgVoteResp] and not [MsgPreVoteResp]), then
      [poll] records the vote and the [res] switch does one of three things:
      win and broadcast, lose and step down, or nothing.

      Each arm lands on [vote_resp_result] directly.  [VoteWon] is
      [becomeLeader] followed by [bcastAppend], whose spec gives *some*
      [repl_sends] list rather than one [App] per peer -- which is what
      [step_win] asks for.  [VoteLost] is [becomeFollower(r.Term, None)], and
      [become_follower s1 s1.(nstate.term) (W64 0)] is verbatim
      [vote_resp_result]'s [lost] branch.  [VotePending] leaves the state at
      [s1] and sends nothing. *)
  Lemma wp_stepCandidate : wp_stepCandidate_body.
  Proof.
    intros_ambient.
    intros cfg r id s m ents sv voters.
    intros Hty Hterm Hrole Hcfg Happ Hhb.
    wp_start as "(Hphys & Hsnap & Hents)".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto. wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
    (* [state = StateCandidate ≠ StatePreCandidate], so [myVoteRespType] is
       [MsgVoteResp]. *)
    rewrite Hrole /state_w64 /StateCandidate.
    rewrite bool_decide_eq_false_2; last w32_ne.
    wp_auto.
    destruct Hty as [Hty|[Hty|[Hty|[Hty|[Hty|Hty]]]]].
    2:{ (* [MsgProp]: no leader to forward to; dropped *)
      rewrite Hty /MsgProp.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys";
       wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
      iApply ("HΦ" $! errPropDropped s true). iFrame "Hphys ErrPropDropped".
      iPureIntro. rewrite /candidate_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; done. }
    2:{ (* [MsgApp]: [becomeFollower(m.Term, m.From)], then
         [handleAppendEntries] *)
      destruct (Happ Hty) as (Hwf & Hnw & Hnorm & Hconf).
      specialize (Hterm (or_intror (or_introl Hty))).
      rewrite Hty /MsgApp.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft__becomeFollower with "[$Hphys]").
      iIntros (pvs) "Hphys". try wp_auto.
      iDestruct ("Hents" with "[]") as "[#Hents Hcap]"; first done.
      wp_apply (wp_raft__handleAppendEntries with "[$Hphys $Hents $Hcap]").
      { exact Hwf. }
      { exact Hnw. }
      { exact Hnorm. }
      { exact Hconf. }
      iIntros (s') "[Hphys %Hres]". try wp_auto.
      iApply ("HΦ" $! interface.nil s' false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /candidate_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; [exfalso; revert H2; w32_ne|].
      case_decide as H3; [|done].
      split; first done. exists pvs. rewrite -Hterm. exact Hres. }
    2:{ (* [MsgHeartbeat]: [becomeFollower(m.Term, m.From)], then
         [handleHeartbeat] *)
      destruct (Hhb Hty) as (Hcommit & Hfrom).
      specialize (Hterm (or_intror (or_intror (or_introl Hty)))).
      rewrite Hty /MsgHeartbeat.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft__becomeFollower with "[$Hphys]").
      iIntros (pvs) "Hphys". try wp_auto.
      wp_apply (wp_raft__handleHeartbeat with "[$Hphys]").
      { exact Hcommit. }
      { exact Hfrom. }
      iIntros "Hphys". try wp_auto.
      iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /candidate_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; [exfalso; revert H2; w32_ne|].
      case_decide as H3; [exfalso; revert H3; w32_ne|].
      case_decide as H4; [|done].
      split; first done. exists pvs. rewrite -Hterm. reflexivity. }
    2:{ (* [MsgBeat], [MsgAppResp], [MsgHeartbeatResp]: no arm *)
      assert (m.(raftpb.Message.Type') ≠ MsgVoteResp ∧
              m.(raftpb.Message.Type') ≠ MsgProp ∧
              m.(raftpb.Message.Type') ≠ MsgApp ∧
              m.(raftpb.Message.Type') ≠ MsgHeartbeat) as (H1 & H2 & H3 & H4).
      { destruct Hty as [Hty|[Hty|Hty]]; rewrite Hty; split_and!; w32_ne. }
      destruct Hty as [Hty|[Hty|Hty]]; rewrite Hty;
        [rewrite /MsgBeat|rewrite /MsgAppResp|rewrite /MsgHeartbeatResp];
        (rewrite bool_decide_eq_false_2; last w32_ne); wp_auto.
      all: iApply ("HΦ" $! interface.nil s false); iFrame "Hphys"; iPureIntro.
      all: rewrite /candidate_step_result decide_False // decide_False //
             decide_False // decide_False // decide_True; [done|].
      all: rewrite Hty; naive_solver. }
    2:{ (* [MsgSnap]: [becomeFollower(m.Term, m.From)], then
         [handleSnapshot] *)
      iDestruct ("Hsnap" with "[//]") as "(%Hscope & #Hsv & #Hvs)".
      specialize (Hterm (or_intror (or_intror (or_intror Hty)))).
      rewrite Hty /MsgSnap.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft__becomeFollower with "[$Hphys]").
      iIntros (pvs) "Hphys". try wp_auto.
      wp_apply (wp_raft__handleSnapshot _ _ _ _ _ sv voters with "[$Hphys $Hsv $Hvs]").
      { done. }
      { done. }
      { exact Hcfg. }
      { exact Hscope. }
      iIntros (s') "[Hphys %Hres]". try wp_auto.
      iApply ("HΦ" $! interface.nil s' false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /candidate_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; [exfalso; revert H2; w32_ne|].
      case_decide as H3; [exfalso; revert H3; w32_ne|].
      case_decide as H4; [exfalso; revert H4; w32_ne|].
      case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
      case_decide as H6; [|done].
      split; first done. exists pvs. rewrite -Hterm. exact Hres. }
    specialize (Hterm (or_introl Hty)).
    (* the type switch: [MsgVoteResp] is none of [MsgProp], [MsgApp],
       [MsgHeartbeat], [MsgSnap], so it falls through to [myVoteRespType].
       Only the first comparison needs help; once [m.Type] is the literal
       [W32 6], [wp_auto] decides the rest by computation. *)
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
    assert (cfg ≠ ∅) as Hcfg_ne by set_solver.
    wp_apply (P.wp_raft__poll _ _ _ _ _ _ _ Hcfg_ne with "[$Hphys]")
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
      iIntros (pvs1) "[Hphys %Hmb]". wp_auto.
      (* [bcastAppend] adds *some* list of [App]s from [id] at the current
         term -- not one per peer; see [spec_raft__bcastAppend.v]. *)
      wp_apply (wp_raft__bcastAppend with "[$Hphys]").
      iIntros (ms pvs) "(Hphys & %Hms & %Hmm)". try wp_auto.
      iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
      (* The postcondition is [⌜result⌝ ∗ ⌜err = nil⌝]; [iFrame "Hphys"]
         does *not* discharge the second, so [iPureIntro] leaves a
         conjunction. *)
      iPureIntro. split; last done.
      rewrite /candidate_step_result. case_decide; [|done]. split; first done.
      exists true, false, ms, pvs.
      split_and!;
        [ intros _; split_and!;
          [ by apply Hwon
          | apply (repl_sends_prvals _ _ pvs1); exact Hms
          | rewrite Hmm; exact Hmb ]
        | intros [=]
        | rewrite /vote_resp_result // ].
    - (* [quorum.VoteLost]: step down at the unchanged term. *)
      rewrite /VoteLost bool_decide_eq_false_2; last w32_ne. wp_auto.
      (* the [r.Term] the code passes is [s1]'s term *)
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      wp_apply (P.wp_raft__becomeFollower with "[$Hphys]").
      iIntros (pvs) "Hphys". try wp_auto.
      iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /candidate_step_result. case_decide; [|done]. split; first done.
      exists false, true, [], pvs.
      split_and!;
        [ intros [=]
        | intros _; by apply Hlost
        | rewrite /vote_resp_result // ].
    - (* [quorum.VotePending]: neither switch arm fires; keep waiting. *)
      rewrite /VotePending bool_decide_eq_false_2; last w32_ne. wp_auto.
      iApply ("HΦ" $! interface.nil s1 false). iFrame "Hphys".
      (* nothing wrote a [Progress]: the values are [s1]'s own *)
      iPureIntro. split; last done.
      rewrite /candidate_step_result. case_decide; [|done]. split; first done.
      exists false, false, [], s1.(nstate.prvals).
      split_and!;
        [ intros [=]
        | intros [=]
        | rewrite /vote_resp_result /s1; by destruct s ].
  Qed.

End StepCandidateProof.
