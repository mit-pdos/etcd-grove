Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__entries.

Module RaftLogEntriesProof (P : RAFTLOG__ENTRIES_POSTULATES) : RAFTLOG__ENTRIES.
Import P.



Set Default Proof Using "Type".

  Lemma wp_raftLog__entries : wp_raftLog__entries_body.
  Proof.
    intros_ambient.
    intros l ls i maxSize Hlo.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]".
    logstate_simpl.
    wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
    case_bool_decide as Hgt.
    - (* [i] is past the end: [nil] and no error; the log is untouched. *)
      wp_auto.
      iApply ("HΦ" $! slice.nil []).
      iFrame "Hlog". iSplitL; first iApply own_slice_nil.
      iPureIntro. split; [intros e He; by apply elem_of_nil in He | apply prefix_nil].
    - wp_auto.
      wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]") as "%li2 [Hlog %Hli2]". logstate_simpl.
      wp_apply (wp_raftLog__slice _ (logstate.mk prev sents uents lcm lap snap) _ _ _ with "[$Hlog]")
        as "%sl %es (Hlog & Hsl & %Hes)".
      { logstate_simpl. word. }
      logstate_simpl.
      destruct Hes as (_ & _ & Hin & Hpre).
      try wp_auto.
      iApply ("HΦ" $! sl es). iFrame "Hlog Hsl". iPureIntro. split; [exact Hin|exact Hpre].
  Qed.

End RaftLogEntriesProof.
