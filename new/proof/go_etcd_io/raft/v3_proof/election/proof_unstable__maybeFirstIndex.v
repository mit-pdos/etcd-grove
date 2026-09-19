Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__maybeFirstIndex.

Module UnstableMaybeFirstIndexProof (P : UNSTABLE__MAYBEFIRSTINDEX_POSTULATES) : UNSTABLE__MAYBEFIRSTINDEX.

  Lemma wp_unstable__maybeFirstIndex : wp_unstable__maybeFirstIndex_body.
  Proof.
    intros_ambient.
    intros u uv.

    intros Hns. wp_start as "Hu". wp_auto.
    rewrite Hns bool_decide_eq_true_2 //=. wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End UnstableMaybeFirstIndexProof.
