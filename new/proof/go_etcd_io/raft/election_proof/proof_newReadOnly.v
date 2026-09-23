Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newReadOnly.

Module NewReadOnlyProof (P : NEWREADONLY_POSTULATES) : NEWREADONLY.

  Lemma wp_newReadOnly : wp_newReadOnly_body.
  Proof.
    intros_ambient.
    intros o rs ro pri.

    wp_start as "Hm". iNamed "Hm". wp_auto.
    wp_apply wp_map_make1 as "%mref Hmref".
    wp_alloc ro' as "Hro'". wp_auto.
    iApply "HΦ". rewrite /own_raft_misc.
    iExists rss, _, ∅, ([] : list loc), prims.
    iFrame "Hro'". simpl.
    iFrame "HreadStates HreadStates_cap Hmref Hpri Hpri_cap".
    iSplitL.
    { iApply own_slice_nil. }
    iApply own_slice_cap_nil.
  Qed.

End NewReadOnlyProof.
