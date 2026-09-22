Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__resetRandomizedElectionTimeout.

Module RaftResetRandomizedElectionTimeoutProof (P : RAFT__RESETRANDOMIZEDELECTIONTIMEOUT_POSTULATES) : RAFT__RESETRANDOMIZEDELECTIONTIMEOUT.

  (** The receiver of the [Intn] call is the global [globalRand], loaded
      through the read-only points-to that [is_pkg_init raft] carries
      ([is_initialized] in base.v); the same package predicate supplies
      [is_lockedRand] for it.  The [+] wraps, and the spec is existential in
      the sum, so nothing about the draw is needed beyond its existence. *)
  Lemma wp_raft__resetRandomizedElectionTimeout : wp_raft__resetRandomizedElectionTimeout_body.
  Proof.
    intros_ambient.
    intros r rv Het.
    wp_start as "Hr".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto.
    wp_apply (P.wp_lockedRand__Intn _ _ Het with "[$HglobalRand]") as "%v %Hv".
    iApply "HΦ". iFrame.
  Qed.

End RaftResetRandomizedElectionTimeoutProof.
