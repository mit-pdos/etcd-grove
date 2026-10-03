Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepFollower.

Module StepFollowerProof (P : STEPFOLLOWER_POSTULATES) : STEPFOLLOWER.
Import P.

  (** By type.  The type switch's first test is against [MsgProp]
      ([W32 2]); rewriting [m.Type] to its literal lets [wp_auto] decide
      the rest by computation.

      - [MsgVoteResp], [MsgBeat], [MsgAppResp], [MsgHeartbeatResp]: no arm
        matches; [return nil].
      - [MsgProp], leaderless: [r.lead == None] holds, the [Infof] reads
        [r.id], [r.Term] and the logger, and the [return] loads
        [ErrProposalDropped] -- a package global, whose points-to
        [is_pkg_init_access] hands out.
      - [MsgProp], with a leader: [disableProposalForwarding] is [false]
        ([wp_raft_load_disableProposalForwarding]), [m.To = r.lead] is a
        store into the local copy of [m], and [send] takes clause (e).
      - [MsgApp]/[MsgHeartbeat]/[MsgSnap]: two stores ([electionElapsed],
        untracked, and [lead]), then [handleAppendEntries]/[handleHeartbeat]/
        [handleSnapshot] at [s <| lead := m.From |>]. *)
  Lemma wp_stepFollower : wp_stepFollower_body.
  Proof.
    intros_ambient.
    intros cfg r id s m ents sv voters.
    intros Hty Hprop Happ Hhb.
    wp_start as "(Hphys & Hsnap & Hents)".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto.
    destruct Hty as [Hty|[Hty|[Hty|[Hty|[Hty|Hty]]]]].
    - (* [MsgVoteResp]: no arm *)
      rewrite Hty /MsgVoteResp.
      rewrite bool_decide_eq_false_2; last w32_ne.
      wp_auto.
      iApply ("HΦ" $! interface.nil s false).
      iFrame "Hphys". iPureIntro.
      rewrite /follower_step_result. case_decide; done.
    - (* [MsgProp] *)
      destruct (Hprop Hty) as (Hfrom0 & Hterm0 & Hlid).
      rewrite Hty /MsgProp.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      wp_apply (wp_raft_load_lead with "Hphys") as "Hphys".
      destruct (decide (s.(nstate.lead) = W64 0)) as [Hlead|Hlead].
      + (* leaderless: dropped *)
        rewrite Hlead bool_decide_eq_true_2 //. wp_auto.
        (wp_apply (wp_raft_load_id with "Hphys") as "Hphys";
         wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
        iApply ("HΦ" $! errPropDropped s true). iFrame "Hphys ErrPropDropped".
        iPureIntro.
        rewrite /follower_step_result Hty.
        case_decide as H1; [exfalso; revert H1; w32_ne|].
        case_decide as H2; [|done]. case_decide as H3; done.
      + (* forwarded to the leader *)
        rewrite bool_decide_eq_false_2 //. wp_auto.
        wp_apply (wp_raft_load_disableProposalForwarding with "Hphys") as "Hphys".
        try wp_auto.
        wp_apply (wp_raft_load_lead with "Hphys") as "Hphys".
        try wp_auto.
        iDestruct ("Hents" with "[]") as "[#Hes _]".
        { iPureIntro. by right. }
        wp_apply (wp_raft__send _ _ _ _ (m <| raftpb.Message.To' := s.(nstate.lead) |>) ents with "[$Hphys $Hes]").
        { exact Hfrom0. }
        { right; right; right; right. split_and!; [done|done|simpl; congruence|reflexivity]. }
        iIntros "Hphys". wp_auto.
        iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
        iPureIntro. split; last done.
        rewrite /follower_step_result Hty.
        case_decide as H1; [exfalso; revert H1; w32_ne|].
        case_decide as H2; [|done]. case_decide as H3; done.
    - (* [MsgApp]: adopt the sender as leader, then [handleAppendEntries] *)
      destruct (Happ Hty) as (Hwf & Hnw & Hnorm & Hconf).
      rewrite Hty /MsgApp.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft_store_electionElapsed with "Hphys") as "Hphys".
      wp_apply (wp_raft_store_lead with "Hphys") as "Hphys".
      iDestruct ("Hents" with "[]") as "[#Hents Hcap]".
      { iPureIntro. by left. }
      wp_apply (wp_raft__handleAppendEntries with "[$Hphys $Hents $Hcap]").
      { exact Hwf. }
      { exact Hnw. }
      { exact Hnorm. }
      { exact Hconf. }
      iIntros (s') "[Hphys %Hres]". try wp_auto.
      iApply ("HΦ" $! interface.nil s' false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /follower_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; [exfalso; revert H2; w32_ne|].
      case_decide as H3; done.
    - (* [MsgHeartbeat]: adopt the sender as leader, then [handleHeartbeat] *)
      destruct (Hhb Hty) as (Hcommit & Hfrom).
      rewrite Hty /MsgHeartbeat.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft_store_electionElapsed with "Hphys") as "Hphys".
      wp_apply (wp_raft_store_lead with "Hphys") as "Hphys".
      wp_apply (wp_raft__handleHeartbeat with "[$Hphys]").
      { exact Hcommit. }
      { exact Hfrom. }
      iIntros "Hphys". try wp_auto.
      iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /follower_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; [exfalso; revert H2; w32_ne|].
      case_decide as H3; [exfalso; revert H3; w32_ne|].
      case_decide as H4; done.
    - (* [MsgBeat], [MsgAppResp], [MsgHeartbeatResp]: no arm *)
      assert (m.(raftpb.Message.Type') ≠ MsgVoteResp ∧
              m.(raftpb.Message.Type') ≠ MsgProp ∧
              m.(raftpb.Message.Type') ≠ MsgApp ∧
              m.(raftpb.Message.Type') ≠ MsgHeartbeat) as (H1 & H2 & H3 & H4).
      { destruct Hty as [Hty|[Hty|Hty]]; rewrite Hty; split_and!; w32_ne. }
      destruct Hty as [Hty|[Hty|Hty]]; rewrite Hty;
        [rewrite /MsgBeat|rewrite /MsgAppResp|rewrite /MsgHeartbeatResp];
        (rewrite bool_decide_eq_false_2; last w32_ne); wp_auto.
      all: iApply ("HΦ" $! interface.nil s false); iFrame "Hphys"; iPureIntro.
      all: rewrite /follower_step_result decide_False // decide_False //
             decide_False // decide_False // decide_True; [done|].
      all: rewrite Hty; naive_solver.
    - (* [MsgSnap]: adopt the sender as leader, then [handleSnapshot] *)
      iDestruct ("Hsnap" with "[//]")
        as "((%Hscope & %Hrole & %Hvotes & %Hcfg) & #Hsv & #Hvs)".
      rewrite Hty /MsgSnap.
      rewrite bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft_store_electionElapsed with "Hphys") as "Hphys".
      wp_apply (wp_raft_store_lead with "Hphys") as "Hphys".
      wp_apply (wp_raft__handleSnapshot _ _ _ _ _ sv voters with "[$Hphys $Hsv $Hvs]").
      { exact Hrole. }
      { exact Hvotes. }
      { exact Hcfg. }
      { exact Hscope. }
      iIntros (s') "[Hphys %Hres]". try wp_auto.
      iApply ("HΦ" $! interface.nil s' false). iFrame "Hphys".
      iPureIntro. split; last done.
      rewrite /follower_step_result Hty.
      case_decide as H1; [exfalso; revert H1; w32_ne|].
      case_decide as H2; [exfalso; revert H2; w32_ne|].
      case_decide as H3; [exfalso; revert H3; w32_ne|].
      case_decide as H4; [exfalso; revert H4; w32_ne|].
      case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
      case_decide as H6; done.
  Qed.

End StepFollowerProof.
