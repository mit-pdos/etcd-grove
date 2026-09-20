Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_big_Int__Int64.

Module BigIntInt64Proof (P : BIG_INT__INT64_POSTULATES) : BIG_INT__INT64.

  (** Trust boundary: an [Axiom] inside the functor rather than an
      [Admitted] [Lemma], so that it still counts as an assumption under
      [Print Assumptions] and in [etc/tcb-report.py].  [math/big] is not
      translated and is not raft; see [spec_big_Int__Int64.v] and
      notes/STATUS.md ("Trust base") for why it may be assumed. *)
  Axiom wp_big_Int__Int64 : wp_big_Int__Int64_body.

End BigIntInt64Proof.
