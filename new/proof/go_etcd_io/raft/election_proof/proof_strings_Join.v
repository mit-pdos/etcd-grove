Require Export New.proof.go_etcd_io.raft.election_proof.postulates_strings_Join.

Module StringsJoinProof (P : STRINGS_JOIN_POSTULATES) : STRINGS_JOIN.

  (** Not translated; see the comment at the spec. *)
  Axiom wp_strings_Join : wp_strings_Join_body.


End StringsJoinProof.
