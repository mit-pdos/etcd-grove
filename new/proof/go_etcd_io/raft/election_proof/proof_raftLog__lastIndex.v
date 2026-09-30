Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.

Module RaftLogLastIndexProof (P : RAFTLOG__LASTINDEX_POSTULATES) : RAFTLOG__LASTINDEX.
Import P.

  Lemma wp_raftLog__lastIndex : wp_raftLog__lastIndex_body.
  Proof.
    intros_ambient.
    intros l ls.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
    assert (Hnw : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') +
                   Z.of_nat (length uents) < 2^64)%Z) by lia.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    split_unstable l lv.
    wp_apply (wp_unstable__maybeLastIndex _ _ _ Hnosnap Hnw
                with "[Huf Huents Huents_cap]")
      as "%li %ok ((Huf & Huents_cap & Huents) & %Hok1 & %Hok2)".
    { rewrite /own_unstable. iFrame. }
    iDestruct ("Hlback" with "Huf") as "Hl".
    destruct (decide (uents = [])) as [He|Hne].
    - rewrite (Hok1 He) /=. wp_auto. rewrite Hstok /=.
      wp_apply ("HLI" with "HStorage") as "%li2 [%Hli HStorage]".
      iApply ("HΦ" $! li2).
      iSplitL "Hl HStorage Huents Huents_cap".
      { iApply (own_raftLog_intro with "Hl HisStorage HStorage Huents Huents_cap"); done. }
      iPureIntro. rewrite He /=. lia.
    - destruct (Hok2 Hne) as [Hokt Hli]. rewrite Hokt /=. wp_auto.
      iApply ("HΦ" $! li).
      iSplitL "Hl HStorage Huents Huents_cap".
      { iApply (own_raftLog_intro with "Hl HisStorage HStorage Huents Huents_cap"); done. }
      iPureIntro. lia.
  Qed.

End RaftLogLastIndexProof.
