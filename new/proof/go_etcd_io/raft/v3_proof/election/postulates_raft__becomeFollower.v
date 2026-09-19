Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceBecomeFollower.

Module Type BECOMEFOLLOWER_POSTULATES.
  Include RESET.  Include TRACEBECOMEFOLLOWER.
End BECOMEFOLLOWER_POSTULATES.
