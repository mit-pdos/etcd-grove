Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeLeader.

Module BecomeLeaderProof (P : BECOMELEADER_POSTULATES) : BECOMELEADER.

  Lemma wp_raft__becomeLeader : wp_raft__becomeLeader_body.
  Proof.
    intros ?????? sem package_sem cfg γ r id s.
    intros Hrole Hcfg. wp_start as "Hphys". iNamed "Hphys". wp_auto.
    (* [becomeLeader] panics on a follower; by assumption we are not one. *)
    assert (state_w64 s.(nstate.role) ≠ W64 0) as Hnf.
    { destruct (s.(nstate.role)) eqn:Hro; try congruence;
        rewrite /state_w64 /StateCandidate /StateLeader;
        intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
    rewrite Hstate bool_decide_eq_false_2 //. wp_auto.
    iAssert (own_raft_phys γ r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys".
    { rewrite /own_raft_phys.
      iExists (rv <| raft.raft.step' := _ |>), msgs, msgsAA, lok. iFrame "∗#%". }
    (* [reset] is called at the unchanged term, so the vote survives *)
    rewrite Hterm.
    wp_apply (P.wp_raft__reset with "[$Hphys]") as "Hphys".
    iNamedSuffix "Hphys" "1".
    assert (rv0.(raft.raft.Vote') = s.(nstate.vote)) as Hvote1'.
    { rewrite Hvote1 /=. rewrite decide_True //. }
    (* [r.tick], [r.lead := r.id], [r.state := StateLeader] *)
    wp_auto.
    rewrite Hid1.
    (* the leader's own [Progress] is marked replicating and recently active *)
    wp_apply (wp_tracker_progress_lookup _ _ _ _ Hcfg with "[$Htrk1]")
      as "%pr [Hpr Hprback]".
    wp_apply (wp_Progress__BecomeReplicate with "[$Hpr]") as "Hpr".
    iDestruct "Hpr" as (recentActive) "[Hra Hrest]".
    wp_auto.
    iAssert (own_progress pr) with "[Hra Hrest]" as "Hpr".
    { rewrite /own_progress. iExists true. iFrame. }
    iDestruct ("Hprback" with "Hpr") as "Htrk1".
    wp_apply (wp_raftLog__lastIndex with "[$Hlog1]") as "%li Hlog1".
    wp_apply (wp_traceBecomeLeader with "[$Hmisc1]") as "Hmisc1".
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto.
    wp_apply (wp_raft__appendEmptyEntry with "[$Hlog1]") as "Hlog1".
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
    wp_auto. rewrite Hlok1.
    wp_apply (wp_Logger__logf with "Hlogger1").
    { rewrite /log_methods. set_solver. }
    iApply "HΦ". rewrite /own_raft_phys /become_leader /=.
    iExists _, msgs0, msgsAA0, lok0.
    simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
    iEval (simpl) in "Htrk1".
    iFrame "Hr1 ∗#%".
    iPureIntro. split_and!; done.
  Qed.

End BecomeLeaderProof.
