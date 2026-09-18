Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__hasNextOrInProgressSnapshot.

Module RaftLogHasNextOrInProgressSnapshotProof (P : RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT_POSTULATES) : RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.

  Lemma wp_raftLog__hasNextOrInProgressSnapshot : wp_raftLog__hasNextOrInProgressSnapshot_body.
  Proof.
    intros_ambient.
    intros l.

    wp_start as "Hlog". iDestruct "Hlog" as (prev sents uents) "Hlog".
    iNamed "Hlog". wp_auto.
    rewrite Hnosnap bool_decide_eq_true_2 //=.
    iApply ("HΦ" $! false). iSplit; last done.
    iExists prev, sents, uents. rewrite /own_raftLog_at. iExists lv.
    iFrame "∗#%".
  Qed.

End RaftLogHasNextOrInProgressSnapshotProof.
