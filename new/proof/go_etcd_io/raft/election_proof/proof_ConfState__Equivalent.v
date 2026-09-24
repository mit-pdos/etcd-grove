Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ConfState__Equivalent.

Module ConfStateEquivalentProof (P : CONFSTATE__EQUIVALENT_POSTULATES) : CONFSTATE__EQUIVALENT.

  (** Not translated; see the comment at the spec. *)
  Axiom wp_ConfState__Equivalent : wp_ConfState__Equivalent_body.


End ConfStateEquivalentProof.
