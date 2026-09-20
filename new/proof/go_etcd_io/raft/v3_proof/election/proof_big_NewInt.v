Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_big_NewInt.

Module BigNewIntProof (P : BIG_NEWINT_POSTULATES) : BIG_NEWINT.

  (** Trust boundary: an [Axiom] inside the functor rather than an
      [Admitted] [Lemma], so that it still counts as an assumption under
      [Print Assumptions] and in [etc/tcb-report.py].  [math/big] is not
      translated and is not raft; see [spec_big_NewInt.v] and
      notes/STATUS.md ("Trust base") for why it may be assumed. *)
  Axiom wp_big_NewInt : wp_big_NewInt_body.

End BigNewIntProof.
