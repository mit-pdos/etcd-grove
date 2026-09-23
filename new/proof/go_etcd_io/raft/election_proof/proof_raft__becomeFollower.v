Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.

Module BecomeFollowerProof (P : BECOMEFOLLOWER_POSTULATES) : BECOMEFOLLOWER.
Import P.

  Lemma wp_raft__becomeFollower : wp_raft__becomeFollower_body.
  Proof.
    intros_ambient.
    intros cfg r id s term lead Hlent.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [r.step := stepFollower] is done; re-seal for [reset]. *)
    iAssert (own_raft_phys cfg r id
               (s <| nstate.stepfn := step_func_of role.Follower |>))
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys".
    { iApply (own_raft_phys_intro _ _ _
                (s <| nstate.stepfn := step_func_of role.Follower |>) with
        "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        done. }
    (* [reset]'s state is left to the frame: given explicitly, it has to be
       matched against [Hphys] up to conversion, which ran for 24 minutes
       before failing (2026-09-22) *)
    wp_apply (P.wp_raft__reset with "[$Hphys]"); first exact Hlent.
    iIntros "Hphys".
    iDestruct "Hphys" as (rv1 msgs1 msgsAA1 lok1) "Hphys".
    iNamedSuffix "Hphys" "1".
    (* [r.tick], [r.lead := lead], [r.state := StateFollower] *)
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    wp_apply wp_traceBecomeFollower. try wp_auto.
    iApply "HΦ".
    (* every pure goal is a field of [become_follower] computed, by
       conversion; do not [simpl in *] here -- the struct carries
       [functions raft.tickElection []], and [simpl] goes into the
       semantics tables (12+ minutes, 2026-09-22) *)
    iApply (own_raft_phys_intro _ _ _ (become_follower s term lead) with
      "Hr1 Hlogger1 Hprs1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
      done.
  Qed.

End BecomeFollowerProof.
