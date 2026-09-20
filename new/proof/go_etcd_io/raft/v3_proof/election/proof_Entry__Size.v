Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Entry__Size.

Module EntrySizeProof (P : ENTRY__SIZE_POSTULATES) : ENTRY__SIZE.

  (** Trust boundary: an [Axiom] inside the functor rather than an
      [Admitted] [Lemma], so that it still counts as an assumption under
      [Print Assumptions].  See the spec file for why it may be assumed. *)
  Axiom wp_Entry__Size : wp_Entry__Size_body.

End EntrySizeProof.
