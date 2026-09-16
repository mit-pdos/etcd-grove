Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeFollower.

Module BecomeFollowerProof (P : BECOMEFOLLOWER_POSTULATES) : BECOMEFOLLOWER.

  Lemma wp_raft__becomeFollower : wp_raft__becomeFollower_body.
  Proof.
    intros_ambient.
    intros cfg r id s term lead.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [r.step := stepFollower] is done; re-seal for [reset]. *)
    iAssert (own_raft_phys_at cfg r id s (functions raft.stepFollower []))
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys".
    { rewrite /own_raft_phys_at.
      iExists (rv <| raft.raft.step' := functions raft.stepFollower [] |>),
        msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
      iPureIntro. reflexivity. }
    wp_apply (P.wp_raft__reset with "[$Hphys]") as "Hphys".
    iNamedSuffix "Hphys" "1".
    (* [r.tick], [r.lead := lead], [r.state := StateFollower] *)
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    wp_apply (wp_traceBecomeFollower with "[$Hmisc1]") as "Hmisc1".
    iApply "HΦ".
    rewrite /own_raft_phys /own_raft_phys_at /become_follower /step_func_of /=.
    iExists _, msgs0, msgsAA0, lok0.
    simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
    iEval (simpl) in "Htrk1".
    iFrame "Hr1 ∗#%".
    (* [lead] and [state] were just assigned, so these are by computation *)
    iPureIntro. split_and!; reflexivity.
  Qed.

End BecomeFollowerProof.
