Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__switchToConfig.

Module SwitchToConfigProof (P : RAFT__SWITCHTOCONFIG_POSTULATES) : RAFT__SWITCHTOCONFIG.
Import P.

  Lemma wp_raft__switchToConfig : wp_raft__switchToConfig_body.
  Proof.
    intros_ambient.
    intros cfg r id s tv cfgv prsm votes prs tv' Hlent Hrole.
    wp_start as "[Hphys Hnew]". iNamed "Hphys".
    iEval (rewrite Hlent) in "Htrk".
    iDestruct (own_tracker_unless_lent_eq with "Htrk") as %Htv.
    wp_auto.
    wp_apply P.wp_traceConfChangeEvent.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (?) "[? _]". try wp_auto. rewrite Hlok. try wp_auto.
    wp_apply (wp_Logger__logf with "Hlogger"); first solve_log_method.
    iAssert (r ↦ rv <| raft.raft.trk' := tv' |>)%I with "[Hr]" as "Hr".
    { rewrite /tv' -Htv. iExact "Hr". }
    iDestruct (access_strict
                 (A := r.[raft.raft.t, "trk"] ↦ (rv <| raft.raft.trk' := tv' |>).(raft.raft.trk'))
                 (A' := r.[raft.raft.t, "trk"] ↦ (rv <| raft.raft.trk' := tv' |>).(raft.raft.trk'))
                 (P := r ↦ rv <| raft.raft.trk' := tv' |>)
                 (P' := r ↦ rv <| raft.raft.trk' := tv' |>)
                 with "Hr") as "[Htrkf Hrback]".
    iAssert (r.[raft.raft.t, "trk"] ↦ tv')%I with "[Htrkf]" as "Htrkf";
      first iExact "Htrkf".
    wp_apply (P.wp_ProgressTracker__ConfState with "[$Htrkf $Hnew]")
      as "%cs %xs (Htrkf & Hnew & Hcs & %Hxs & %Hcs)".
    iDestruct ("Hrback" with "Htrkf") as "Hr".
    iDestruct (own_tracker_progress_map with "Hnew") as "(#Hprs & %Hdom & Hnew)".
    try wp_auto.
    assert (rv.(raft.raft.state') ≠ W64 2) as Hns.
    { rewrite Hstate. destruct s.(nstate.role) eqn:Hro; rewrite /= /StateFollower /StateCandidate;
        [| |congruence]; intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    wp_apply (wp_map_lookup2 with "Hprs") as "_".
    destruct (prs !! rv.(raft.raft.id')) as [pr|] eqn:Hlk; simpl; wp_auto.
    - iDestruct (own_tracker_lookup _ _ _ _ _ _ Hlk with "Hnew") as "[Hpr Hprback]".
      iDestruct "Hpr" as (pv iv) "Hpr". iNamed "Hpr".
      wp_auto.
      rewrite Hnolearner.
      iDestruct ("Hprback" with "[Hpv Hinfl]") as "Hnew".
      { iExists pv, iv. rewrite /own_progress. iFrame "∗%". }
      wp_auto.
      rewrite (bool_decide_eq_false_2 (rv.(raft.raft.state') = W64 2)); last exact Hns.
      wp_auto.
      iPoseProof (own_raftLog_unless_lent tv' rv.(raft.raft.raftLog')) as "Hnolog".
      iPoseProof (own_tracker_unless_lent cfg tv' s.(nstate.votes) s.(nstate.progress))
        as "Hnotrk".
      iDestruct (own_raft_phys_intro _ _ _ (s <| nstate.lent := Some tv' |>) with
        "Hr Hlogger Hnotrk Hnolog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc")
        as "Hphys"; [done ..|].
      iSpecialize ("HΦ" $! cs xs with "[$Hphys $Hnew $Hcs]"); first done.
      iExactEq "HΦ". reflexivity.
    - rewrite (bool_decide_eq_false_2 (rv.(raft.raft.state') = W64 2)); last exact Hns.
      wp_auto.
      rewrite (bool_decide_eq_false_2 (rv.(raft.raft.state') = W64 2)); last exact Hns.
      wp_auto.
      iPoseProof (own_raftLog_unless_lent tv' rv.(raft.raft.raftLog')) as "Hnolog".
      iPoseProof (own_tracker_unless_lent cfg tv' s.(nstate.votes) s.(nstate.progress))
        as "Hnotrk".
      iDestruct (own_raft_phys_intro _ _ _ (s <| nstate.lent := Some tv' |>) with
        "Hr Hlogger Hnotrk Hnolog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc")
        as "Hphys"; [done ..|].
      iSpecialize ("HΦ" $! cs xs with "[$Hphys $Hnew $Hcs]"); first done.
      iExactEq "HΦ". reflexivity.
  Qed.

End SwitchToConfigProof.
