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
    intros Hty Hterm Hrole Hcfg Happ Hhb Hpvnw.
    wp_start as "(Hphys & Hsnap & Hents)".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto.
    (* [myVoteRespType]: [MsgPreVoteResp] for a pre-candidate, [MsgVoteResp]
       for a candidate; the two arms are joined *)
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
      (λ v, ⌜ v = execute_val ⌝ ∗ own_raft_phys cfg r id s ∗
            myVoteRespType_ptr ↦
              (if bool_decide (s.(nstate.role) = prole.PreCandidate)
               then MsgPreVoteResp else MsgVoteResp) ∗
            r_ptr ↦ r)%I
      with "[Hphys myVoteRespType r]").
    { wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      destruct Hrole as [Hr|Hr]; rewrite Hr.
      - rewrite /state_w64 /StateCandidate bool_decide_eq_false_2; last w32_ne.
        wp_auto. rewrite bool_decide_eq_false_2; last discriminate.
        iSplitR; first done. iFrame.
      - rewrite /state_w64 /StatePreCandidate bool_decide_eq_true_2 //.
        wp_auto. rewrite bool_decide_eq_true_2 //.
        iSplitR; first done. iFrame. }
    iIntros (v) "(-> & Hphys & myVoteRespType & r)".
    (* kept opaque below, so that the arms' [rewrite bool_decide_eq_…] find
       the program's comparisons and not this one *)
    remember (if bool_decide (s.(nstate.role) = prole.PreCandidate)
              then MsgPreVoteResp else MsgVoteResp) as mvr eqn:Hmvr.
    (* without [bool_decide]s, which [case_decide] would pick up *)
    assert (Hmp : s.(nstate.role) = prole.PreCandidate → mvr = W32 18)
      by (intros Hp; rewrite Hmvr bool_decide_eq_true_2 //).
    assert (Hmc : s.(nstate.role) ≠ prole.PreCandidate → mvr = W32 6)
      by (intros Hp; rewrite Hmvr bool_decide_eq_false_2 //).
    clear Hmvr.
    wp_auto.
    destruct Hty as [Hty|[Hty|[Hty|[Hty|[Hty|[Hty|Hty]]]]]].
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
      (* [myVoteRespType] is one of the two response types, neither of these *)
      all: destruct (decide (s.(nstate.role) = prole.PreCandidate)) as [Hp|Hp];
        [ pose proof (Hmp Hp) as Hm | pose proof (Hmc Hp) as Hm ];
        rewrite Hm; wp_auto.
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
    2:{ (* [MsgPreVoteResp] (2026-10-04) *)
      assert (Hty18 : m.(raftpb.Message.Type') = W32 18) by exact Hty.
      rewrite Hty18.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      destruct Hrole as [Hr|Hr].
      - (* a candidate: [myVoteRespType] is [MsgVoteResp]; a stale
           pre-vote response, ignored *)
        assert (Hm : mvr = W32 6) by (apply Hmc; rewrite Hr; discriminate).
        rewrite Hm. wp_auto.
        iApply ("HΦ" $! interface.nil s false). iFrame "Hphys".
        iPureIntro. split; last done.
        rewrite /candidate_step_result Hty.
        case_decide as H1; [exfalso; revert H1; w32_ne|].
        case_decide as H2; [exfalso; revert H2; w32_ne|].
        case_decide as H3; [exfalso; revert H3; w32_ne|].
        case_decide as H4; [exfalso; revert H4; w32_ne|].
        case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
        case_decide as H6; [exfalso; revert H6; w32_ne|].
        case_decide as H7; [|done].
        split; first done. rewrite decide_False //. rewrite Hr. discriminate.
      - (* a pre-candidate: [poll], then win, lose or wait *)
        assert (Hm : mvr = W32 18) by (apply Hmp; exact Hr).
        rewrite Hm. wp_auto.
        assert (cfg ≠ ∅) as Hcfg_ne by set_solver.
        wp_apply (P.wp_raft__poll _ _ _ _ _ _ _ Hcfg_ne with "[$Hphys]")
          as "%g %rj0 %res (Hphys & %Hres & %Hwon & %Hlost)".
        (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
        set (s1 := s <| nstate.votes :=
                     record_vote s.(nstate.votes) m.(raftpb.Message.From')
                       (negb m.(raftpb.Message.Reject')) |>).
        assert (Hres_pv : ∀ s' (won lost : bool) peers pvs,
                  (won = true → is_quorum cfg (granted s1.(nstate.votes)) ∧
                                peers ≡ₚ elements (cfg ∖ {[id]})) →
                  (lost = true → ¬ is_quorum cfg (cfg ∖ rejected s1.(nstate.votes))) →
                  s' = prevote_resp_result id s m.(raftpb.Message.From')
                         m.(raftpb.Message.Reject') won lost peers <| nstate.prvals := pvs |> →
                  candidate_step_result cfg id s m ents sv false s').
        { intros s' won lost peers pvs Hw Hl ->.
          rewrite /candidate_step_result Hty.
          case_decide as H1; [exfalso; revert H1; w32_ne|].
          case_decide as H2; [exfalso; revert H2; w32_ne|].
          case_decide as H3; [exfalso; revert H3; w32_ne|].
          case_decide as H4; [exfalso; revert H4; w32_ne|].
          case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
          case_decide as H6; [exfalso; revert H6; w32_ne|].
          case_decide as H7; [|done].
          split; first done. rewrite decide_True //.
          exists won, lost, peers, pvs. cbv zeta.
          split_and!; [exact Hw|exact Hl|reflexivity]. }
        destruct Hres as [Hres|[Hres|Hres]]; rewrite Hres.
        + (* [quorum.VoteWon]: the real election, [campaign(campaignElection)] *)
          rewrite /VoteWon bool_decide_eq_true_2 //. wp_auto.
          wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
          assert (s1.(nstate.role) = prole.PreCandidate) as Hrole1 by exact Hr.
          rewrite Hrole1 /state_w64 /StatePreCandidate bool_decide_eq_true_2 //.
          wp_auto.
          assert (Hnl1 : s1.(nstate.role) ≠ prole.Leader) by (rewrite Hrole1; discriminate).
          assert (Hnw1 : uint.Z s1.(nstate.term) + 1 < 2 ^ 64) by exact (Hpvnw Hr Hty).
          wp_apply (P.wp_raft__campaign _ _ _ _ _ Hnl1 Hcfg Hnw1 with "[$Hphys]")
            as "%peers %pvs [%Hpeers Hphys]".
          assert (Hce : campaignElection ≠ campaignPreElection) by done.
          rewrite (bool_decide_eq_false_2 _ Hce).
          iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
          iPureIntro. split; last done.
          eapply (Hres_pv _ true false peers pvs); [|by intros|done].
          intros _. split; [by apply Hwon|exact Hpeers].
        + (* [quorum.VoteLost]: step down at the unchanged term *)
          rewrite /VoteLost bool_decide_eq_false_2; last w32_ne. wp_auto.
          wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
          wp_apply (P.wp_raft__becomeFollower with "[$Hphys]").
          iIntros (pvs) "Hphys". try wp_auto.
          iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
          iPureIntro. split; last done.
          eapply (Hres_pv _ false true [] pvs); [by intros|intros _; by apply Hlost|done].
        + (* [quorum.VotePending]: keep waiting *)
          rewrite /VotePending bool_decide_eq_false_2; last w32_ne. wp_auto.
          iApply ("HΦ" $! interface.nil s1 false). iFrame "Hphys".
          iPureIntro. split; last done.
          eapply (Hres_pv _ false false [] s1.(nstate.prvals)); [by intros|by intros|].
          rewrite /prevote_resp_result /s1. by destruct s. }
    specialize (Hterm (or_introl Hty)).
    (* the type switch: [MsgVoteResp] is none of [MsgProp], [MsgApp],
       [MsgHeartbeat], [MsgSnap], so it falls through to [myVoteRespType].
       Only the first comparison needs help; once [m.Type] is the literal
       [W32 6], [wp_auto] decides the rest by computation. *)
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
    destruct Hrole as [Hrole|Hrole]; last first.
    { (* a pre-candidate: [myVoteRespType] is [MsgPreVoteResp]; a vote
         response is ignored *)
      assert (Hm : mvr = W32 18) by (apply Hmp; exact Hrole).
      rewrite Hm. wp_auto.
      iApply ("HΦ" $! interface.nil s false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /candidate_step_result. case_decide; [|done]. split; first done.
      rewrite decide_True //. }
    assert (Hm : mvr = W32 6) by (apply Hmc; rewrite Hrole; discriminate).
    rewrite Hm. wp_auto.
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
      assert (s1.(nstate.role) = prole.Candidate) as Hrole1 by exact Hrole.
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
      rewrite decide_False; last (rewrite Hrole; discriminate).
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
      rewrite decide_False; last (rewrite Hrole; discriminate).
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
      rewrite decide_False; last (rewrite Hrole; discriminate).
      exists false, false, [], s1.(nstate.prvals).
      split_and!;
        [ intros [=]
        | intros [=]
        | rewrite /vote_resp_result /s1; by destruct s ].
  Qed.

End StepCandidateProof.
