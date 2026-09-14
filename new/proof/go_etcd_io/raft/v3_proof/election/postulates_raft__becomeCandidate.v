(** * Postulates: [raft.raft__becomeCandidate]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.

Module Type BECOMECANDIDATE_POSTULATES.
  Include RESET.
End BECOMECANDIDATE_POSTULATES.
