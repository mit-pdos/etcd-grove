(** * Link: [raft.raft__poll]

    [raft__poll] is in scope but unfinished: the hole is the [Admitted] in
    [proof_raft__poll.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__poll.

Module PollPostulates : POLL_POSTULATES.
End PollPostulates.

Module Poll := PollProof PollPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments Poll.wp_raft__poll {_ _ _ _ _ _ _ _}.
