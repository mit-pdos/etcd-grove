Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__maybeCommit.

Module RaftLogMaybeCommitProof (P : RAFTLOG__MAYBECOMMIT_POSTULATES) : RAFTLOG__MAYBECOMMIT.
Import P.

  Lemma wp_raftLog__maybeCommit : wp_raftLog__maybeCommit_body.
  Proof.
    intros_ambient.
    intros l ls aid.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & [%Hcm %Hap] & Hback)".
    logstate_simpl.
    wp_auto.
    destruct (decide (aid.(raft.entryID.term') = W64 0)) as [Ht0|Ht0].
    { (* [at.term == 0]: no *)
      rewrite (bool_decide_eq_true_2 (aid.(raft.entryID.term') = W64 0)) //. wp_auto.
      iApply "HΦ". iDestruct ("Hback" with "Hl") as "$". iPureIntro.
      symmetry. apply bool_decide_eq_false_2. intros (Hne & _ & _). by apply Hne. }
    rewrite (bool_decide_eq_false_2 (aid.(raft.entryID.term') = W64 0)) //. wp_auto.
    rewrite Hcm.
    destruct (decide (uint.Z lcm < uint.Z aid.(raft.entryID.index'))%Z) as [Hlt|Hge].
    2:{ (* [at.index <= committed]: no *)
      rewrite (bool_decide_eq_false_2 (uint.Z lcm < uint.Z aid.(raft.entryID.index'))%Z) //.
      wp_auto.
      iApply "HΦ". iDestruct ("Hback" with "Hl") as "$". iPureIntro.
      symmetry. apply bool_decide_eq_false_2. intros (_ & Hlt & _). by apply Hge. }
    rewrite (bool_decide_eq_true_2 (uint.Z lcm < uint.Z aid.(raft.entryID.index'))%Z) //.
    wp_auto.
    iDestruct ("Hback" with "Hl") as "Hlog".
    wp_apply (wp_raftLog__matchTerm _ (logstate.mk prev sents uents lcm lap snap) _
                with "[$Hlog]") as "%b [Hlog %Hb]". logstate_simpl.
    destruct b.
    - (* [matchTerm]: commit.  [commitTo]'s premise from the match. *)
      symmetry in Hb. apply bool_decide_eq_true_1 in Hb.
      pose proof (plog_term_at_Some_range _ _ _ _ Hb) as Hrange.
      wp_auto.
      wp_apply (wp_raftLog__commitTo _ (logstate.mk prev sents uents lcm lap snap) aid.(raft.entryID.index')
                  ltac:(cbn [logstate.prev logstate.sents logstate.uents]; lia) with "[$Hlog]") as "Hlog".
      iApply "HΦ". simpl.
      rewrite /plog_commit_to decide_True; last lia.
      iFrame. iPureIntro. symmetry. apply bool_decide_eq_true_2.
      split_and!; [done | lia | done].
    - wp_auto.
      iApply "HΦ". iFrame. iPureIntro. symmetry. apply bool_decide_eq_false_2.
      intros (_ & _ & Hm). symmetry in Hb. apply bool_decide_eq_false_1 in Hb. done.
  Qed.

End RaftLogMaybeCommitProof.
