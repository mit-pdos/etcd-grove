Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__bcastAppend.

Module StepCandidatePostulates : STEPCANDIDATE_POSTULATES.
  Include Poll.
  Include BecomeLeader.
  Include BecomeFollower.  Include RaftBcastAppend.
End StepCandidatePostulates.

Module StepCandidate := StepCandidateProof StepCandidatePostulates.
