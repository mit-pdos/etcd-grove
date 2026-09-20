Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_limitSize.

Module LimitSizeProof (P : LIMITSIZE_POSTULATES) : LIMITSIZE.
Import P.

  Lemma wp_limitSize : wp_limitSize_body.
  Proof.
    intros_ambient.
    intros s es dq maxSize.
  Admitted.

End LimitSizeProof.
