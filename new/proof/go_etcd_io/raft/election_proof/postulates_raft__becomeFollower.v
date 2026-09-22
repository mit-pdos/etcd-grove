Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceBecomeFollower.

Module Type BECOMEFOLLOWER_POSTULATES.
  Include RESET.  Include TRACEBECOMEFOLLOWER.
End BECOMEFOLLOWER_POSTULATES.
