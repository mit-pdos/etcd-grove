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
    intros cfg r id s.
    wp_start as "Hphys".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto.
    (* [r.electionTimeout] is read twice, and [own_raft_phys] does not track
       it, so the two reads are unrelated -- all [Intn] needs of its
       argument is the bound, which comes with each read *)
    wp_apply (wp_raft_load_electionTimeout with "Hphys") as "%et1 [Hphys %Het1]".
    wp_apply (wp_raft_load_electionTimeout with "Hphys") as "%et2 [Hphys %Het2]".
    wp_apply (P.wp_lockedRand__Intn _ _ Het2 with "[$HglobalRand]")
      as "%v %Hv".
    wp_apply (wp_raft_store_randomizedElectionTimeout with "Hphys") as "Hphys".
    iApply "HΦ". iFrame.
  Qed.

End RaftResetRandomizedElectionTimeoutProof.
