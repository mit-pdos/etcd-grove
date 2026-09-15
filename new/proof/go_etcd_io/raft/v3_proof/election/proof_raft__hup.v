Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__hup.

Module HupProof (P : HUP_POSTULATES) : HUP.

  Lemma wp_raft__hup : wp_raft__hup_body.
  Proof.
  Admitted.

End HupProof.
