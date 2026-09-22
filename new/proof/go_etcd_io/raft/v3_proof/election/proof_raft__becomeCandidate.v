Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeCandidate.

Module BecomeCandidateProof (P : BECOMECANDIDATE_POSTULATES) : BECOMECANDIDATE.
Import P.

  Lemma wp_raft__becomeCandidate : wp_raft__becomeCandidate_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    intros Hrole Hlent. wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [becomeCandidate] panics on a leader; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateFollower /StateCandidate;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    rewrite Hstate bool_decide_eq_false_2 //. wp_auto.
    iAssert (own_raft_phys cfg r id
               (s <| nstate.stepfn := step_func_of role.Candidate |>))
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys".
    { iApply (own_raft_phys_intro _ _ _
                (s <| nstate.stepfn := step_func_of role.Candidate |>) with
        "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        done. }
    (* [reset] is called at [r.Term + 1] *)
    rewrite Hterm.
    (* [reset]'s state is left to the frame: given explicitly, it has to be
       matched against [Hphys] up to conversion, which ran for 24 minutes
       before failing (2026-09-22) *)
    wp_apply (P.wp_raft__reset with "[$Hphys]"); first exact Hlent.
    iIntros "Hphys".
    iDestruct "Hphys" as (rv1 msgs1 msgsAA1 lok1) "Hphys".
    iNamedSuffix "Hphys" "1".
    (* [r.tick], [r.Vote := r.id], [r.state := StateCandidate] *)
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    wp_apply (wp_traceBecomeCandidate with "[$Hmisc1]") as "Hmisc1".
    iApply "HΦ".
    iApply (own_raft_phys_intro _ _ _ (become_candidate id s) with
      "Hr1 Hlogger1 Hprs1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
      done.
  Qed.

End BecomeCandidateProof.
