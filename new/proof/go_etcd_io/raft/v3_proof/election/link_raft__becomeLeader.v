(** * Link: [raft.raft__becomeLeader]

    [raft__becomeLeader] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.

Module BecomeLeaderPostulates : BECOMELEADER_POSTULATES.
  Include Reset.
End BecomeLeaderPostulates.

Module BecomeLeader := BecomeLeaderProof BecomeLeaderPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments BecomeLeader.wp_raft__becomeLeader {_ _ _ _ _ _ _ _}.
