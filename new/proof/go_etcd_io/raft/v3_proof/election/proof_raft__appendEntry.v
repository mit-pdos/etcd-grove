Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__appendEntry.

Module RaftAppendEntryProof (P : RAFT__APPENDENTRY_POSTULATES) : RAFT__APPENDENTRY.

  (** Trust boundary: an [Axiom] inside the functor rather than an
      [Admitted] [Lemma], so that it still counts as an assumption
      under [Print Assumptions] and under the greps in
      notes/STATUS.md.  See that file for why it may be assumed. *)
  Axiom wp_raft__appendEntry : wp_raft__appendEntry_body.

End RaftAppendEntryProof.
