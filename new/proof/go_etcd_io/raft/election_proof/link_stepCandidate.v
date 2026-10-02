Require Export New.proof.go_etcd_io.raft.election_proof.proof_stepCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__handleHeartbeat.

Module StepCandidatePostulates : STEPCANDIDATE_POSTULATES.
  Include Poll.
  Include BecomeLeader.
  Include BecomeFollower.  Include RaftBcastAppend.
  Include RaftHandleAppendEntries.
  Include RaftHandleHeartbeat.
End StepCandidatePostulates.

Module StepCandidate := StepCandidateProof StepCandidatePostulates.
