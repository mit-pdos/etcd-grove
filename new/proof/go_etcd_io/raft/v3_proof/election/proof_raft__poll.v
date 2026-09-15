Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.

Module PollProof (P : POLL_POSTULATES) : POLL.

  Lemma wp_raft__poll : wp_raft__poll_body.
  Proof.
  Admitted.

End PollProof.
