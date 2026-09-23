Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__snapshot.

Module RaftLogSnapshotProof (P : RAFTLOG__SNAPSHOT_POSTULATES) : RAFTLOG__SNAPSHOT.

  Lemma wp_raftLog__snapshot_at : wp_raftLog__snapshot_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents esu.

    wp_start as "H". iNamed "H". iNamed "Hlog".
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    wp_auto.
    (* [l.unstable.snapshot] is [null], so the early return is dead *)
    rewrite Hnosnap bool_decide_eq_true_2 //=.
    wp_auto. rewrite Hstok /=.
    wp_apply ("HSnap" with "[$HStorage $Hesu]") as "%snap %err [HStorage %Herr]".
    iApply ("HΦ" $! snap err).
    iSplitL; last done.
    rewrite /own_raftLog_at. iExists lv. rewrite Hstok. iFrame "∗#%".
    by iPureIntro.
  Qed.

End RaftLogSnapshotProof.
