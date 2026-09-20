Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__hasUnappliedConfChanges.

Module RaftHasUnappliedConfChangesProof (P : RAFT__HASUNAPPLIEDCONFCHANGES_POSTULATES) : RAFT__HASUNAPPLIEDCONFCHANGES.
Import P.

  Lemma wp_raft__hasUnappliedConfChanges : wp_raft__hasUnappliedConfChanges_body.
  Proof.
    intros_ambient.
    intros r rv.
  Admitted.

End RaftHasUnappliedConfChangesProof.
