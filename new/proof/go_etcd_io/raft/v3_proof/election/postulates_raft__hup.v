(** * Postulates: [raft.raft__hup]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.

Module Type HUP_POSTULATES.
  Include CAMPAIGN.
End HUP_POSTULATES.
