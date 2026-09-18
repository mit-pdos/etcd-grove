Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceBecomeFollower.

Module BecomeFollowerPostulates : BECOMEFOLLOWER_POSTULATES.
  Include Reset.  Include TraceBecomeFollower.
End BecomeFollowerPostulates.

Module BecomeFollower := BecomeFollowerProof BecomeFollowerPostulates.
