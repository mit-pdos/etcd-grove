Require Export New.proof.go_etcd_io.raft.election_proof.proof_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__handleHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.

Module StepFollowerPostulates : STEPFOLLOWER_POSTULATES.
  Include RaftHandleAppendEntries.
  Include RaftHandleHeartbeat.
  Include Send.
End StepFollowerPostulates.

Module StepFollower := StepFollowerProof StepFollowerPostulates.
