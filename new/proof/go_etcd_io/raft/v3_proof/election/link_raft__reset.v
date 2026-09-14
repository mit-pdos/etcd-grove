(** * Link: [raft.raft__reset]

    [raft__reset] is in scope but unfinished: the hole is the [Admitted] in
    [proof_raft__reset.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__reset.

Module ResetPostulates : RESET_POSTULATES.
End ResetPostulates.

Module Reset := ResetProof ResetPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments Reset.wp_raft__reset {_ _ _ _ _ _ _ _}.
