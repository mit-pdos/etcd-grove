Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeCandidate.

Module BecomeCandidateProof (P : BECOMECANDIDATE_POSTULATES) : BECOMECANDIDATE.

  Lemma wp_raft__becomeCandidate : wp_raft__becomeCandidate_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    intros Hrole. wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [becomeCandidate] panics on a leader; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateFollower /StateCandidate;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    rewrite Hstate bool_decide_eq_false_2 //. wp_auto.
    iAssert (own_raft_phys cfg r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys".
    { rewrite /own_raft_phys.
      iExists (rv <| raft.raft.step' := _ |>), msgs, msgsAA, lok. iFrame "∗#%". }
    (* [reset] is called at [r.Term + 1] *)
    rewrite Hterm.
    wp_apply (P.wp_raft__reset with "[$Hphys]") as "Hphys".
    iNamedSuffix "Hphys" "1".
    (* [r.tick], [r.Vote := r.id], [r.state := StateCandidate] *)
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    wp_apply (wp_traceBecomeCandidate with "[$Hmisc1]") as "Hmisc1".
    iApply "HΦ". rewrite /own_raft_phys /become_candidate /=.
    iExists _, msgs0, msgsAA0, lok0.
    simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
    iEval (simpl) in "Htrk1".
    iFrame "Hr1 ∗#%".
    iPureIntro; reflexivity.
  Qed.

End BecomeCandidateProof.
