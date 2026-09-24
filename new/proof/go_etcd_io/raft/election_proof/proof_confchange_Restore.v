Require Export New.proof.go_etcd_io.raft.election_proof.postulates_confchange_Restore.

Module ConfchangeRestoreProof (P : CONFCHANGE_RESTORE_POSTULATES) : CONFCHANGE_RESTORE.

  (** Not translated; see the comment at the spec. *)
  Axiom wp_confchange_Restore : wp_confchange_Restore_body.


End ConfchangeRestoreProof.
