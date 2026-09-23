Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__entries.

Module RaftLogEntriesProof (P : RAFTLOG__ENTRIES_POSTULATES) : RAFTLOG__ENTRIES.
Import P.



Set Default Proof Using "Type".

  Lemma wp_raftLog__entries : wp_raftLog__entries_body.
  Proof.
    intros_ambient.
    intros l ls i maxSize Hpg Hlo.
    destruct ls as [prev sents uents lcm lap lpg]; logstate_simpl; subst lpg.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]"; first done.
    logstate_simpl.
    wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap None) eq_refl with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
    case_bool_decide as Hgt.
    - (* [i] is past the end: an empty page and no error.  The log is not
         opened at all, so [l ↦ lv] has to be split out of it by hand. *)
      wp_auto.
      iNamed "Hlog".
      iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
      iApply ("HΦ" $! slice.nil [] (DfracOwn 1)).
      iSplitL; last iApply own_slice_nil.
      rewrite /own_raftLog /=. iExists lv. iFrame "Hl". iSplitR; first done.
      iSplitR; first done.
      iIntros "_". rewrite /own_raftLog_core. iFrame "∗#%".
    - wp_auto.
      wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap None) eq_refl with "[$Hlog]") as "%li2 [Hlog %Hli2]". logstate_simpl.
      wp_apply (wp_raftLog__slice _ (logstate.mk prev sents uents lcm lap None) _ _ _ eq_refl with "[$Hlog]")
        as "%sl %es %dq (Hlog & Hsl & %Hes)".
      { logstate_simpl. word. }
      logstate_simpl.
      try wp_auto.
      iApply ("HΦ" $! sl es dq). iFrame "Hlog Hsl".
  Qed.

End RaftLogEntriesProof.
