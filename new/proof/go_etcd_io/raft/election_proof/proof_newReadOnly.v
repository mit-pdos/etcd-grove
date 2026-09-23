Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newReadOnly.

Module NewReadOnlyProof (P : NEWREADONLY_POSTULATES) : NEWREADONLY.

  Lemma wp_newReadOnly : wp_newReadOnly_body.
  Proof.
    intros_ambient.
    intros o.

    wp_start. wp_auto.
    wp_apply wp_map_make1 as "%mref Hmref".
    wp_alloc ro' as "Hro'". wp_auto.
    iApply "HΦ". rewrite /own_read_only.
    iExists _, ∅, ([] : list loc).
    iFrame "Hro'". simpl.
    iFrame "Hmref".
    iSplitL.
    { iApply own_slice_nil. }
    iApply own_slice_cap_nil.
  Qed.

End NewReadOnlyProof.
