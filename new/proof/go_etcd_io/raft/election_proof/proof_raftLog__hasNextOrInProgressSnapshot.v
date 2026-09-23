Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__hasNextOrInProgressSnapshot.

Module RaftLogHasNextOrInProgressSnapshotProof (P : RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT_POSTULATES) : RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.

  Lemma wp_raftLog__hasNextOrInProgressSnapshot : wp_raftLog__hasNextOrInProgressSnapshot_body.
  Proof.
    intros_ambient.
    intros l ls Hpg.
    destruct ls as [prev sents uents lcm lap lpg]; logstate_simpl; subst lpg.
    wp_start as "Hlog".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
    rewrite Hnosnap bool_decide_eq_true_2 //=.
    iApply ("HΦ" $! false). iSplit; last done.
    iApply own_raftLog_unfold. iExists lv. rewrite /own_raftLog_core.
    iFrame "∗#%".
  Qed.

End RaftLogHasNextOrInProgressSnapshotProof.
