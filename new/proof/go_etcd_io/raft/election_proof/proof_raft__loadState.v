Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__loadState.

Module LoadStateProof (P : RAFT__LOADSTATE_POSTULATES) : RAFT__LOADSTATE.
Import P.

  Lemma wp_raft__loadState : wp_raft__loadState_body.
  Proof.
    intros_ambient.
    intros cfg r id s tv ls hs Hlent Hpg Hc.
    destruct ls as [prev sents uents lcm lap lpg]; logstate_simpl; subst lpg.
    wp_start as "[Hphys HL]".
    wp_auto.
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raftLog_unfold with "HL") as (lv) "(Hl & %Hcm & %Hap & Hcore)".
    logstate_simpl.
    wp_auto.
    rewrite bool_decide_eq_false_2; last (subst; word). try wp_auto.
    iAssert (own_raftLog s.(nstate.log) (logstate.mk prev sents uents lcm lap None))
      with "[Hl Hcore]" as "HL".
    { iApply own_raftLog_unfold. iExists lv. iFrame. done. }
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    wp_apply (P.wp_raftLog__lastIndex with "[$HL]") as "%li [HL %Hli]"; first done.
    logstate_simpl.
    rewrite bool_decide_eq_false_2; last word.
    try wp_auto.
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raftLog_unfold with "HL") as (lv2) "(Hl & %Hcm2 & %Hap2 & Hcore)".
    logstate_simpl.
    try wp_auto.
    wp_apply (wp_raft_store_Term with "Hphys") as "Hphys".
    try wp_auto.
    wp_apply (wp_raft_store_Vote with "Hphys") as "Hphys".
    try wp_auto.
    iApply "HΦ". iFrame "Hphys".
    iApply (own_raftLog_unfold _ prev sents uents hs.(raftpb.HardState.Commit') lap).
    iExists _. iFrame "Hl". iSplitR; [done|]. iSplitR; [done|].
    rewrite /own_raftLog_core. iEval (rewrite /own_raftLog_core) in "Hcore".
    iDestruct "Hcore" as "(%Hidx & %Hnowrap & #HisStorage & HStorage & %Hoffset &
      Huents & Huents_cap & %Hnosnap & %Hncc & %Happlied & %Hcommitted)".
    logstate_simpl. simpl. iFrame "∗#%". iPureIntro. simpl. subst. rewrite Hcm2 in Happlied. lia.
  Qed.

End LoadStateProof.
