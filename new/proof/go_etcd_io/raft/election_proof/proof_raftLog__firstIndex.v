Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__firstIndex.

Module RaftLogFirstIndexProof (P : RAFTLOG__FIRSTINDEX_POSTULATES) : RAFTLOG__FIRSTINDEX.
Import P.

  (** Two exits: a pending snapshot answers from [unstable.maybeFirstIndex]
      ([prev] is the snapshot's id, [log_store_ok]); otherwise
      [Storage.FirstIndex], whose boundary is [prev]. *)
  Lemma wp_raftLog__firstIndex : wp_raftLog__firstIndex_body.
  Proof.
    intros_ambient.
    intros l ls.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    split_unstable l lv.
    wp_apply (wp_unstable__maybeFirstIndex _ _ _ snap with "[Huf Huents Huents_cap]")
      as "%fi %ok ((Huf & Huents_cap & Huents) & %Hok)".
    { rewrite /own_unstable. iFrame "∗#". }
    iDestruct ("Hlback" with "Huf") as "Hl".
    destruct Hok as [-> Hfi].
    destruct snap as [sid|].
    - rewrite (bool_decide_eq_true_2 (Some sid ≠ None)) //. wp_auto.
      iApply ("HΦ" $! fi).
      iSplitL "Hl HStorage Huents Huents_cap".
      { reseal_raftLog. }
      pose proof Hstore as (-> & _ & Hsid).
      iPureIntro. rewrite (Hfi sid eq_refl). word.
    - rewrite (bool_decide_eq_false_2 (None ≠ None)); last (by intros ?). wp_auto. rewrite Hstok /=.
      pose proof Hstore as (Hsp & _ & _).
      wp_apply ("HFI" with "HStorage") as "%fi2 [%Hfi2 HStorage]".
      iApply ("HΦ" $! fi2).
      iSplitL "Hl HStorage Huents Huents_cap".
      { reseal_raftLog. }
      iPureIntro. rewrite Hsp in Hfi2. word.
  Qed.

End RaftLogFirstIndexProof.
