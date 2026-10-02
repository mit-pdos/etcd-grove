Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__switchToConfig.

Module SwitchToConfigProof (P : RAFT__SWITCHTOCONFIG_POSTULATES) : RAFT__SWITCHTOCONFIG.
Import P.

  Lemma wp_raft__switchToConfig : wp_raft__switchToConfig_body.
  Proof.
    intros_ambient.
    intros cfg0 cfg r id s cfgv prsm prs Hrole.
    wp_start as "[Hphys Hnew]".
    wp_auto.
    wp_apply P.wp_traceConfChangeEvent.
    (* [r.trk.Config = cfg; r.trk.Progress = trk]: the one change of
       configuration, through [own_raft_phys_reconfig] *)
    iDestruct (own_raft_phys_reconfig cfg0 cfg _ _ _ with "Hphys")
      as (tv) "(Htrkf & Hold & Hback)".
    wp_auto.
    iDestruct (own_tracker_reconfig with "Hold Hnew") as (pvs) "Htrk".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    set s' := s <| nstate.progress := prs |> <| nstate.prvals := pvs |>.
    (* the log line: [r.id], [r.trk.Config] *)
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_tracker_same _ _ _ s' with "Hphys")
      as (tv1) "(Htrkf & Htrk & Hback)".
    wp_auto.
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    wp_raft_log.
    (* [cs := r.trk.ConfState()] *)
    iDestruct (own_raft_phys_tracker_same _ _ _ s' with "Hphys")
      as (tv2) "(Htrkf & Htrk & Hback)".
    wp_apply (P.wp_ProgressTracker__ConfState with "[$Htrkf $Htrk]")
      as "%cs %xs (Htrkf & Htrk & Hcs & %Hxs & %Hcs)".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    try wp_auto.
    (* [pr, ok := r.trk.Progress[r.id]] *)
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_tracker_same _ _ _ s' with "Hphys")
      as (tv3) "(Htrkf & Htrk & Hback)".
    iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
    iEval (cbn [trk.prs]) in "Hprs".
    wp_auto.
    wp_apply (wp_map_lookup2 with "Hprs") as "_".
    (* [r.isLearner = ok && pr.IsLearner] is [false]: every voter's
       [Progress] has [IsLearner = false] *)
    assert (state_w64 s'.(nstate.role) ≠ W64 2) as Hns.
    { simpl. destruct s.(nstate.role) eqn:Hro; rewrite /= /StateFollower /StateCandidate;
        [| |congruence]; intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    destruct (prs !! id) as [pr|] eqn:Hlk; simpl; try wp_auto.
    - iDestruct (own_tracker_lookup_same _ _ (trk.mk _ _ _) _ _ Hlk with "Htrk")
        as (p) "(_ & Hpr & Hprback)".
      iNamed "Hpr".
      pose proof Habs as Hnolearner.
      apply progress_abs_Some in Hnolearner as (Hnolearner & _).
      try wp_auto.
      rewrite Hnolearner.
      iDestruct ("Hprback" with "[Hpv Hinfl]") as "Htrk".
      { iExists _. iFrame "∗%". }
      iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
      wp_apply (wp_raft_store_isLearner with "Hphys") as "Hphys".
      try wp_auto.
      wp_apply (wp_raft_load_isLearner with "Hphys") as "Hphys". try wp_auto.
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      rewrite (bool_decide_eq_false_2 (state_w64 _ = W64 2)); last exact Hns.
      try wp_auto.
      iSpecialize ("HΦ" $! cs xs pvs with "[$Hphys $Hcs]"); first done.
      iExactEq "HΦ". reflexivity.
    - iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
      wp_apply (wp_raft_store_isLearner with "Hphys") as "Hphys".
      try wp_auto.
      (* [!ok] is [true]: the [||] does not load [r.isLearner], and
         [r.state] is loaded by both [if]s *)
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      rewrite (bool_decide_eq_false_2 (state_w64 _ = W64 2)); last exact Hns.
      try wp_auto.
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      rewrite (bool_decide_eq_false_2 (state_w64 _ = W64 2)); last exact Hns.
      try wp_auto.
      iSpecialize ("HΦ" $! cs xs pvs with "[$Hphys $Hcs]"); first done.
      iExactEq "HΦ". reflexivity.
  Qed.

End SwitchToConfigProof.
