Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__resetRandomizedElectionTimeout.

Module RaftResetRandomizedElectionTimeoutProof (P : RAFT__RESETRANDOMIZEDELECTIONTIMEOUT_POSTULATES) : RAFT__RESETRANDOMIZEDELECTIONTIMEOUT.

  Lemma wp_raft__resetRandomizedElectionTimeout : wp_raft__resetRandomizedElectionTimeout_body.
  Proof.
    intros_ambient.
    intros r rv.

    wp_start as "Hr". wp_auto.
    Show.
  Admitted.

End RaftResetRandomizedElectionTimeoutProof.
