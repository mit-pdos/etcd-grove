Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__matchTerm.

Module RaftLogMatchTermProof (P : RAFTLOG__MATCHTERM_POSTULATES) : RAFTLOG__MATCHTERM.
Import P.

  Lemma wp_raftLog__matchTerm : wp_raftLog__matchTerm_body.
  Proof.
    intros_ambient.
    intros l ls id.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    wp_start as "H". iNamed "H". wp_auto.
    wp_apply (wp_raftLog__term _ (logstate.mk prev sents uents lcm lap) _ with "[$Hlog]")
      as "%t %err (Hlog & %Herr & %Ht & _)". logstate_simpl.
    destruct err as [eok|].
    - (* [err != nil]: [id.index] is out of range, so [plog_term_at] is [None] *)
      wp_pure. wp_auto.
      iApply "HΦ". iFrame. iPureIntro. symmetry. apply bool_decide_eq_false_2.
      rewrite /plog_matches. intros Hm. apply plog_term_at_Some_range in Hm.
      rewrite /plog_last_index_Z length_app in Hm.
      assert (interface.ok eok = interface.nil) as Hc by (apply Herr; lia).
      discriminate Hc.
    - specialize (Ht eq_refl). wp_pure. wp_auto.
      iApply "HΦ". iFrame. iPureIntro. apply bool_decide_ext. rewrite /plog_matches Ht.
      split; [by intros -> | by intros [=]].
  Qed.

End RaftLogMatchTermProof.
