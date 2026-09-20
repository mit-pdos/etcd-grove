Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_entsSize.

Module EntsSizeProof (P : ENTSSIZE_POSTULATES) : ENTSSIZE.
Import P.

  Lemma wp_entsSize : wp_entsSize_body.
  Proof.
    intros_ambient.
    intros s es dq.
  Admitted.

End EntsSizeProof.
