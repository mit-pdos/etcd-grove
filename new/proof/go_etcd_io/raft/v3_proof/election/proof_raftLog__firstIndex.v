Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__firstIndex.

Module RaftLogFirstIndexProof (P : RAFTLOG__FIRSTINDEX_POSTULATES) : RAFTLOG__FIRSTINDEX.
Import P.

  Lemma wp_raftLog__firstIndex_at : wp_raftLog__firstIndex_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents.

    wp_start as "H". iNamed "H". iNamed "Hlog". wp_auto.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    split_unstable l lv.
    wp_apply (wp_unstable__maybeFirstIndex _ _ Hnosnap with "[$Huf]") as "%fi Huf".
    iDestruct ("Hlback" with "Huf") as "Hl".
    wp_auto. rewrite Hstok /=.
    wp_apply ("HFI" with "HStorage") as "%fi2 [%Hfi HStorage]".
    iApply ("HΦ" $! fi2).
    iSplitL "Hl HStorage Huents Huents_cap".
    { rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
      iFrame "∗#%". all: (iPureIntro; done). }
    iPureIntro. word.
  Qed.

End RaftLogFirstIndexProof.
