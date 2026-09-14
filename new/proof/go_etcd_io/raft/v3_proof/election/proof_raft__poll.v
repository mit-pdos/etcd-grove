(** * Proof: [raft.raft__poll] against its spec

    Opaquely ascribed, so the proof term is sealed: callers can depend on
    nothing but the spec.  The binders arrive by [intros] rather than
    [Context] -- the lemma's type is closed, so there are no section variables
    to discharge and no [Collection W] is needed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.

Module PollProof (P : POLL_POSTULATES) : POLL.

  Lemma wp_raft__poll : wp_raft__poll_body.
  Proof.
  Admitted.

End PollProof.
