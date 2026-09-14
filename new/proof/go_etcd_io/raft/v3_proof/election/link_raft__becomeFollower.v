(** * Link: [raft.raft__becomeFollower]

    [raft__becomeFollower] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.

Module BecomeFollowerPostulates : BECOMEFOLLOWER_POSTULATES.
  Include Reset.
End BecomeFollowerPostulates.

Module BecomeFollower := BecomeFollowerProof BecomeFollowerPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments BecomeFollower.wp_raft__becomeFollower {_ _ _ _ _ _ _ _}.
