Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeFirstIndex.

Module UnstableMaybeFirstIndexProof (P : UNSTABLE__MAYBEFIRSTINDEX_POSTULATES) : UNSTABLE__MAYBEFIRSTINDEX.

  Lemma wp_unstable__maybeFirstIndex : wp_unstable__maybeFirstIndex_body.
  Proof.
    intros_ambient.
    intros u uv uents.

    intros Hns. wp_start as "Hun". iNamed "Hun". wp_auto.
    rewrite Hns bool_decide_eq_true_2 //=. wp_auto.
    iApply "HΦ". rewrite /own_unstable. iFrame.
  Qed.

End UnstableMaybeFirstIndexProof.
