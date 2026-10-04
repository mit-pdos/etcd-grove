Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomePreCandidate.

Module BecomePreCandidateProof (P : BECOMEPRECANDIDATE_POSTULATES) : BECOMEPRECANDIDATE.
Import P.

  Lemma wp_raft__becomePreCandidate : wp_raft__becomePreCandidate_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    intros Hrole. wp_start as "Hphys". wp_auto.
    (* [becomePreCandidate] panics on a leader; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateFollower /StateCandidate /StatePreCandidate;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
    rewrite bool_decide_eq_false_2 //. wp_auto.
    (* [r.step := stepCandidate] *)
    wp_apply (wp_raft_store_step with "Hphys") as "Hphys".
    (* [r.trk.ResetVotes()], on the tracker the accessor hands out; put back
       at the empty tally *)
    iDestruct (own_raft_phys_tracker with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
    wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
      as "%votesRef [Htrkf Htrk]".
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    try wp_auto.
    (* [r.tick], [r.lead := None], [r.state := StatePreCandidate] *)
    (wp_apply (wp_raft_store_tick with "Hphys") as "Hphys";
     wp_apply (wp_raft_store_lead with "Hphys") as "Hphys";
     wp_apply (wp_raft_store_state _ _ _ _ prole.PreCandidate with "Hphys") as "Hphys").
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys";
     wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    iApply "HΦ".
    (* the stores give [become_precandidate] up to the order of the record
       updates; no [simpl]: the state carries a [functions …] value *)
    iApply (own_raft_phys_eq with "Hphys"). by destruct s.
  Qed.

End BecomePreCandidateProof.
