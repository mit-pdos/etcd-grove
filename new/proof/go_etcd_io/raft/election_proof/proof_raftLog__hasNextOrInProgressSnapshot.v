Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__hasNextOrInProgressSnapshot.

Module RaftLogHasNextOrInProgressSnapshotProof (P : RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT_POSTULATES) : RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.

  Lemma wp_raftLog__hasNextOrInProgressSnapshot : wp_raftLog__hasNextOrInProgressSnapshot_body.
  Proof.
    intros_ambient.
    intros l ls.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "Hlog".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
    destruct snap as [sid|].
    - iPoseProof "Husnap" as "Hus". iEval (rewrite own_snap_Some) in "Hus". iDestruct "Hus" as (sv) "[#Hsv _]".
      iDestruct (typed_pointsto_not_null with "Hsv") as %Hnn.
      rewrite (bool_decide_eq_false_2
                 (lv.(raft.raftLog.unstable').(raft.unstable.snapshot') = null) Hnn) /=.
      iApply ("HΦ" $! true). iSplit.
      + reseal_raftLog.
      + iPureIntro. first [done | rewrite (bool_decide_eq_true_2 (Some sid ≠ None)) //].
    - iPoseProof "Husnap" as "Hus". iEval (rewrite own_snap_None) in "Hus". iDestruct "Hus" as %Hnosnap.
      rewrite (bool_decide_eq_true_2
                 (lv.(raft.raftLog.unstable').(raft.unstable.snapshot') = null) Hnosnap) /=.
      iApply ("HΦ" $! false). iSplit.
      + reseal_raftLog.
      + iPureIntro. first [done | rewrite (bool_decide_eq_false_2 (None ≠ None)) //].
  Qed.

End RaftLogHasNextOrInProgressSnapshotProof.
