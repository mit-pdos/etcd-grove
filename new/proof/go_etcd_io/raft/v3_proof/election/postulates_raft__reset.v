(** * Postulates: [raft.raft__reset]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__reset.

Module Type RESET_POSTULATES.
End RESET_POSTULATES.
