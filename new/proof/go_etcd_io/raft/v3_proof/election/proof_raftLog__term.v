Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__term.

Module RaftLogTermProof (P : RAFTLOG__TERM_POSTULATES) : RAFTLOG__TERM.
Import P.

  Lemma wp_raftLog__term_at : wp_raftLog__term_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents i.

    intros Hi. wp_start as "H". iNamed "H". iNamed "Hlog". wp_auto.
    assert (Hnw : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') +
                   Z.of_nat (length uents) < 2^64)%Z) by lia.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT)".
    split_unstable l lv.
    wp_apply (wp_unstable__maybeTerm _ _ _ _ Hnosnap Hnw with "[$Huf $Huents]")
      as "%t %ok (Huf & Huents & %Hok)".
    iDestruct ("Hlback" with "Huf") as "Hl".
    destruct ok.
    - wp_auto.
      iApply ("HΦ" $! t). rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
      iFrame "∗#%". all: (iPureIntro; done).
    - assert (Hnotin : ¬ (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                          ≤ uint.Z i <
                          uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                          + Z.of_nat (length uents))%Z).
      { intros Hc. apply Hok in Hc. done. }
      assert (Hile : (uint.Z i ≤ uint.Z prev.(raft.entryID.index')
                      + Z.of_nat (length sents))%Z) by lia.
      wp_auto.
      iAssert (own_raftLog_at l prev sents uents)
        with "[Hl HStorage Huents Huents_cap]" as "Hlog".
      { rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
        iFrame "∗#%". all: (iPureIntro; done). }
      wp_apply (wp_raftLog__firstIndex_at with "[$Hlog]") as "%fi [Hlog %Hfi]".
      assert (Hb1 : bool_decide (uint.Z (word.add i (W64 1)) < uint.Z fi)%Z = false).
      { apply bool_decide_eq_false_2. word. }
      rewrite Hb1 /=. wp_auto.
      wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
      assert (Hb2 : bool_decide (uint.Z li < uint.Z i)%Z = false).
      { apply bool_decide_eq_false_2. lia. }
      rewrite Hb2 /=. wp_auto.
      assert (Hrange : (uint.Z prev.(raft.entryID.index') ≤ uint.Z i ≤
                        uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents))%Z)
        by lia.
      clear Hnotin Hnw Hok Hoffset Hnosnap Hstok Happlied Hcommitted
            Hidx Hnowrap HnoConfChange Hb1 Hb2 Hfi Hli Hile.
      iClear "HisStorage HLI HFI HT".
      clear lv isv fi li.
      iNamed "Hlog". wp_auto.
      iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
      { iExact "HisStorage". }
      iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT)".
      rewrite Hstok /=.
      wp_apply ("HT" $! prev sents i with "[$HStorage]").
      { iPureIntro. lia. }
      iIntros (t2) "[%Ht2 HStorage]".
      wp_auto.
      iApply ("HΦ" $! t2). rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
      iFrame "∗#%". all: (iPureIntro; done).
  Qed.

End RaftLogTermProof.
