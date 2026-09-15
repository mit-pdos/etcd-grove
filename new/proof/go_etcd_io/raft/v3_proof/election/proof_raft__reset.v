Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.

  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
  Admitted.

End ResetProof.
