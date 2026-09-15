Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.

Module BecomeLeaderPostulates : BECOMELEADER_POSTULATES.
  Include Reset.
End BecomeLeaderPostulates.

Module BecomeLeader := BecomeLeaderProof BecomeLeaderPostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments BecomeLeader.wp_raft__becomeLeader {_ _ _ _ _ _ _ _}.
