Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__snapshot.

Module RaftLogSnapshotProof (P : RAFTLOG__SNAPSHOT_POSTULATES) : RAFTLOG__SNAPSHOT.

  Lemma wp_raftLog__snapshot : wp_raftLog__snapshot_body.
  Proof.
    intros_ambient.
    intros l ls esu.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
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
    iApply own_raftLog_unfold. iExists lv. rewrite /own_raftLog_core Hstok.
    iFrame "∗#%".
    by iPureIntro.
  Qed.

End RaftLogSnapshotProof.
