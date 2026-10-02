Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__findConflictByTerm.

Module RaftLogFindConflictByTermProof (P : RAFTLOG__FINDCONFLICTBYTERM_POSTULATES) : RAFTLOG__FINDCONFLICTBYTERM.
Import P.

  Lemma wp_raftLog__findConflictByTerm : wp_raftLog__findConflictByTerm_body.
  Proof.
    intros_ambient.
    intros l ls index term.
    wp_start as "H". iNamed "H". wp_auto.
    iAssert (∃ (idx : w64),
      "index" ∷ index_ptr ↦ idx ∗
      "Hlog" ∷ own_raftLog l ls ∗
      "%Hidx" ∷ ⌜ (uint.Z idx ≤ uint.Z index)%Z ⌝)%I
      with "[index Hlog]" as "IH".
    { iFrame. done. }
    wp_for "IH".
    wp_if_destruct.
    - wp_apply (wp_raftLog__term _ ls _ with "[$Hlog]")
        as "%t %err (Hlog & %Herr & %Ht & _)".
      destruct err as [eok|].
      + wp_pure. wp_auto. wp_for_post.
        iApply "HΦ". iFrame. done.
      + wp_pure. wp_auto.
        wp_if_destruct.
        * wp_for_post. iApply "HΦ". iFrame. done.
        * wp_for_post. iFrame. iPureIntro. word.
    - iApply "HΦ". iFrame. iPureIntro. word.
  Qed.

End RaftLogFindConflictByTermProof.
