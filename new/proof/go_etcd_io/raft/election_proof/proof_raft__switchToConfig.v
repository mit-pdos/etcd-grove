Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__switchToConfig.

Module SwitchToConfigProof (P : RAFT__SWITCHTOCONFIG_POSTULATES) : RAFT__SWITCHTOCONFIG.
Import P.

  Lemma wp_raft__switchToConfig : wp_raft__switchToConfig_body.
  Proof.
    intros_ambient.
    intros cfg r id s tv cfgv prsm votes prs tv' Hrole.
    wp_start as "[Hphys Hnew]".
    wp_auto.
    wp_apply P.wp_traceConfChangeEvent.
    (* [r.trk.Config = cfg; r.trk.Progress = trk], through the tracker field *)
    iDestruct (own_raft_phys_trk_lent with "Hphys") as "[Htrkf Htrkback]".
    wp_auto.
    iDestruct ("Htrkback" $! tv' with "Htrkf") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ (s <| nstate.lent := Some tv' |>) with "Hphys")
      as "Hphys"; first by destruct s.
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_trk_lent with "Hphys") as "[Htrkf Htrkback]".
    wp_auto.
    iDestruct ("Htrkback" $! tv' with "Htrkf") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ (s <| nstate.lent := Some tv' |>) with "Hphys")
      as "Hphys"; first by destruct s.
    wp_raft_log.
    (* [cs := r.trk.ConfState()] *)
    iDestruct (own_raft_phys_trk_lent with "Hphys") as "[Htrkf Htrkback]".
    wp_apply (P.wp_ProgressTracker__ConfState with "[$Htrkf $Hnew]")
      as "%cs %xs (Htrkf & Hnew & Hcs & %Hxs & %Hcs)".
    iDestruct (own_tracker_progress_map with "Hnew") as "(#Hprs & %Hdom & Hnew)".
    iDestruct ("Htrkback" $! tv' with "Htrkf") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ (s <| nstate.lent := Some tv' |>) with "Hphys")
      as "Hphys"; first by destruct s.
    try wp_auto.
    (* [pr, ok := r.trk.Progress[r.id]] *)
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_trk_lent with "Hphys") as "[Htrkf Htrkback]".
    wp_auto.
    iDestruct ("Htrkback" $! tv' with "Htrkf") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ (s <| nstate.lent := Some tv' |>) with "Hphys")
      as "Hphys"; first by destruct s.
    wp_apply (wp_map_lookup2 with "Hprs") as "_".
    (* [r.isLearner = ok && pr.IsLearner] is [false]: every voter's
       [Progress] has [IsLearner = false] *)
    assert (state_w64 (s <| nstate.lent := Some tv' |>).(nstate.role) ≠ W64 2) as Hns.
    { simpl. destruct s.(nstate.role) eqn:Hro; rewrite /= /StateFollower /StateCandidate;
        [| |congruence]; intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    destruct (prs !! id) as [pr|] eqn:Hlk; simpl; try wp_auto.
    - iDestruct (own_tracker_lookup _ _ _ _ _ _ Hlk with "Hnew") as "[Hpr Hprback]".
      iDestruct "Hpr" as (pv iv) "Hpr". iNamed "Hpr".
      try wp_auto.
      rewrite Hnolearner.
      iDestruct ("Hprback" with "[Hpv Hinfl]") as "Hnew".
      { iExists pv, iv. rewrite /own_progress. iFrame "∗%". }
      wp_apply (wp_raft_store_isLearner with "Hphys") as "Hphys".
      try wp_auto.
      wp_apply (wp_raft_load_isLearner with "Hphys") as "Hphys". try wp_auto.
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      rewrite (bool_decide_eq_false_2 (state_w64 _ = W64 2)); last exact Hns.
      try wp_auto.
      iSpecialize ("HΦ" $! cs xs with "[$Hphys $Hnew $Hcs]"); first done.
      iExactEq "HΦ". reflexivity.
    - wp_apply (wp_raft_store_isLearner with "Hphys") as "Hphys".
      try wp_auto.
      (* [!ok] is [true]: the [||] does not load [r.isLearner], and
         [r.state] is loaded by both [if]s *)
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      rewrite (bool_decide_eq_false_2 (state_w64 _ = W64 2)); last exact Hns.
      try wp_auto.
      wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
      rewrite (bool_decide_eq_false_2 (state_w64 _ = W64 2)); last exact Hns.
      try wp_auto.
      iSpecialize ("HΦ" $! cs xs with "[$Hphys $Hnew $Hcs]"); first done.
      iExactEq "HΦ". reflexivity.
  Qed.

End SwitchToConfigProof.
