Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newReadOnly.

Module NewReadOnlyProof (P : NEWREADONLY_POSTULATES) : NEWREADONLY.

  Lemma wp_newReadOnly : wp_newReadOnly_body.
  Proof.
    intros_ambient.
    intros o.

    wp_start. wp_auto.
    wp_apply wp_map_make1 as "%mref Hmref".
    wp_alloc ro' as "Hro'". wp_auto.
    iApply "HΦ". rewrite /own_ReadOnly.
    iExists _, [].
    iFrame "Hro'". simpl.
    iFrame "Hmref".
    iSplit; first done.
    iSplit; first done.
    iSplitL.
    { iApply own_slice_nil. }
    iSplitL.
    { iApply own_slice_cap_nil. }
    done.
  Qed.

End NewReadOnlyProof.
