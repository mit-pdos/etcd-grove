Require Export New.proof.go_etcd_io.raft.election_proof.postulates_rand_Int.

Module RandIntProof (P : RAND_INT_POSTULATES) : RAND_INT.

  (** Trust boundary: an [Axiom] inside the functor rather than an
      [Admitted] [Lemma], so that it still counts as an assumption under
      [Print Assumptions] and in [etc/tcb-report.py].  This is the RNG,
      which notes/STATUS.md ("Trust base") lists as assumable; see
      [spec_rand_Int.v] for what exactly is claimed and why. *)
  Axiom wp_rand_Int : wp_rand_Int_body.

End RandIntProof.
