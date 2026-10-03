Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.

Module RaftLogLastIndexProof (P : RAFTLOG__LASTINDEX_POSTULATES) : RAFTLOG__LASTINDEX.
Import P.

  (** Three exits: a non-empty unstable suffix; an empty one with a pending
      snapshot, whose index is [prev]'s ([log_store_ok]); an empty one
      without, where [Storage.LastIndex] is [prev.index + |stored|] and
      [stored = sents]. *)
  Lemma wp_raftLog__lastIndex : wp_raftLog__lastIndex_body.
  Proof.
    intros_ambient.
    intros l ls.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
    assert (Hnw : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') +
                   Z.of_nat (length uents) < 2^64)%Z) by lia.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    split_unstable l lv.
    wp_apply (wp_unstable__maybeLastIndex _ _ _ snap Hnw
                with "[Huf Huents Huents_cap]")
      as "%li %ok ((Huf & Huents_cap & Huents) & %Hok1 & %Hok2)".
    { rewrite /own_unstable. iFrame "∗#". }
    iDestruct ("Hlback" with "Huf") as "Hl".
    destruct (decide (uents = [])) as [He|Hne].
    - destruct (Hok1 He) as [-> Hli].
      destruct snap as [sid|].
      + (* the pending snapshot's index *)
        rewrite (bool_decide_eq_true_2 (Some sid ≠ None)) //. wp_auto.
        iApply ("HΦ" $! li).
        iSplitL "Hl HStorage Huents Huents_cap".
        { reseal_raftLog. }
        pose proof Hstore as (-> & -> & _).
        iPureIntro. rewrite (Hli sid eq_refl) He /=. lia.
      + rewrite (bool_decide_eq_false_2 (None ≠ None)); last (by intros ?). wp_auto. rewrite Hstok /=.
        pose proof Hstore as (Hsp & _ & Hstored_eq).
        wp_apply ("HLI" with "HStorage") as "%li2 [%Hli2 HStorage]".
        iApply ("HΦ" $! li2).
        iSplitL "Hl HStorage Huents Huents_cap".
        { reseal_raftLog. }
        iPureIntro. rewrite Hsp -(Hstored_eq He) in Hli2. rewrite He /=. lia.
    - destruct (Hok2 Hne) as [Hokt Hli]. rewrite Hokt /=. wp_auto.
      iApply ("HΦ" $! li).
      iSplitL "Hl HStorage Huents Huents_cap".
      { reseal_raftLog. }
      iPureIntro. lia.
  Qed.

End RaftLogLastIndexProof.
