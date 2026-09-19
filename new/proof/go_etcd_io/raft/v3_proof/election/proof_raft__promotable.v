Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__promotable.

Module RaftPromotableProof (P : RAFT__PROMOTABLE_POSTULATES) : RAFT__PROMOTABLE.
Import P.

  Lemma wp_raft__promotable : wp_raft__promotable_body.
  Proof.
    intros_ambient.
    intros cfg r rv votes.

  Admitted.

End RaftPromotableProof.
