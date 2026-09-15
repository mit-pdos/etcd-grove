Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.

Module BecomeFollowerPostulates : BECOMEFOLLOWER_POSTULATES.
  Include Reset.
End BecomeFollowerPostulates.

Module BecomeFollower := BecomeFollowerProof BecomeFollowerPostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments BecomeFollower.wp_raft__becomeFollower {_ _ _ _ _ _ _ _}.
