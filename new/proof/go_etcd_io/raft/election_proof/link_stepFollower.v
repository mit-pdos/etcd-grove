Require Export New.proof.go_etcd_io.raft.election_proof.proof_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__handleAppendEntries.

Module StepFollowerPostulates : STEPFOLLOWER_POSTULATES.
  Include RaftHandleAppendEntries.
End StepFollowerPostulates.

Module StepFollower := StepFollowerProof StepFollowerPostulates.
