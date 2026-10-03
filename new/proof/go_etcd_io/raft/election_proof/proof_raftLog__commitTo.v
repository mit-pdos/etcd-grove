Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__commitTo.

Module RaftLogCommitToProof (P : RAFTLOG__COMMITTO_POSTULATES) : RAFTLOG__COMMITTO.
Import P.

  Lemma wp_raftLog__commitTo : wp_raftLog__commitTo_body.
  Proof.
    intros_ambient.
    intros l ls tocommit Hle.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    rewrite /plog_last_index_Z length_app in Hle.
    wp_start as "H". iNamed "H".
    iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & [%Hcm %Hap] & Hback)".
    logstate_simpl.
    wp_auto.
    destruct (decide (uint.Z lcm < uint.Z tocommit)%Z) as [Hlt|Hge].
    - rewrite bool_decide_eq_true_2; last (rewrite Hcm; done).
      wp_auto.
      iDestruct ("Hback" with "Hl") as "Hlog".
      wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]")
        as "%li [Hlog %Hli]". logstate_simpl.
      rewrite bool_decide_eq_false_2; last lia.
      wp_auto.
      clear Hcm Hap lv.
      iNamed "Hlog". iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
      logstate_simpl.
      wp_auto.
      iApply "HΦ".
      rewrite /plog_commit_to decide_True //.
      reseal_raftLog.
      all: pose proof (f_equal uint.Z Hcm) as HcmZ; simpl;
        first [lia | (intros Hs; eapply stored_snap_ok_commit; [|exact (Hssnap Hs)]; simpl; lia)].
    - rewrite bool_decide_eq_false_2; last (rewrite Hcm; lia).
      wp_auto.
      iApply "HΦ".
      rewrite /plog_commit_to decide_False //.
      by iApply "Hback".
  Qed.

End RaftLogCommitToProof.
