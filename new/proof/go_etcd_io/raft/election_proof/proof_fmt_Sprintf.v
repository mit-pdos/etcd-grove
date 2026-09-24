Require Export New.proof.go_etcd_io.raft.election_proof.postulates_fmt_Sprintf.

Module FmtSprintfProof (P : FMT_SPRINTF_POSTULATES) : FMT_SPRINTF.

  (** Not translated; see the comment at the spec. *)
  Axiom wp_fmt_Sprintf : wp_fmt_Sprintf_body.


End FmtSprintfProof.
