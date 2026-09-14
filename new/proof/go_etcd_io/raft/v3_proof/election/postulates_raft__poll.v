(** * Postulates: [raft.raft__poll]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__poll.

Module Type POLL_POSTULATES.
End POLL_POSTULATES.
